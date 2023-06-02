import "transfer.search";
import "transfer.heuristic";
import "util.logging";
signature TRANSFER =
sig
  type goal = Pattern.pattern
  val applyTransferSchemaForGoal : State.T -> InterCSpace.tSchemaData -> goal -> State.T
  val applyTransferSchema : State.T -> InterCSpace.tSchemaData -> State.T Seq.seq
  val singleStepTransfer : State.T -> State.T Seq.seq
  val splitKnowledge : Construction.construction -> Construction.construction list
  val structureTransfer : int option * int option * int option -> bool -> bool -> Pattern.pattern option -> State.T -> State.T Seq.seq
  val agreeEmbeddings : State.T Seq.seq -> (string * string) list list -> State.T Seq.seq
  val quickTransfer : int option * int option * int option -> bool -> Pattern.pattern option -> State.T -> State.T Seq.seq
  (*val sanitize : ''a option list list-> ''a list*)
  val isolateT : (string*string) list ->  (string*string) list
  val propType : (string*string) -> (string*string)
  val embeddingPartial : Type.typeSystem -> Pattern.pattern -> (Pattern.pattern list* ((CSpace.token * CSpace.token) list)) -> (Pattern.pattern* ((CSpace.token * CSpace.token) list)) option
  val crawlWrap : (Pattern.pattern* (((string * Type.typ)*(string* Type.typ)) list)) -> (Type.typ * Type.typ) list
  (*val zipCon : Pattern.pattern -> 'a list -> (Pattern.pattern * 'a) list
  val inLookup : string -> ((string * Type.typ)*(string* Type.typ)) list -> bool
  val findLk : string -> ((string * Type.typ)*(string* Type.typ)) list -> Type.typ
  one of below can be removed*)
  (*val zipNested : Pattern.pattern list list -> ((CSpace.token * CSpace.token) list) list list-> (Pattern.pattern *((CSpace.token * CSpace.token) list)) list list
  *)val zip: 'a list -> 'b list -> ('a*'b) list
 (* val zipRsLk : Pattern.pattern -> (CSpace.token * CSpace.token) list -> (Pattern.pattern * ((CSpace.token * CSpace.token) list))*)
 val analogySearch : int option * int option * int option
                          -> bool
                          -> bool
                          -> Pattern.pattern
                          -> State.T
                          -> State.T Seq.seq

 (* val iterativeStructureTransfer : bool -> Pattern.pattern option
                                        -> State.T -> State.T Seq.seq*)
(*)
  val targetedTransfer : Pattern.pattern
                            -> State.T -> State.T Seq.seq*)

  val masterTransfer : int option * int option * int option
                          -> bool
                          -> bool
                          -> bool
                          -> Pattern.pattern option
                          -> State.T
                          -> State.T Seq.seq

  val initState : CSpace.conSpecData -> (* Source Constructor Specification *)
                  CSpace.conSpecData -> (* Target Constructor Specification *)
                  CSpace.conSpecData -> (* Inter-space Constructor Specification *)
                  bool -> (* use inverse transfer schemas *)
                  Knowledge.base -> (* Transfer and Inference schemas *)
                  Construction.construction -> (* The construction to transform *)
                  Construction.construction -> (* The goal to satisfy *)
                  State.T
  val applyTransfer:
      CSpace.conSpecData -> (* Source Constructor Specification *)
      CSpace.conSpecData -> (* Target Constructor Specification *)
      CSpace.conSpecData -> (* Inter-space Constructor Specification *)
      Knowledge.base -> (* Transfer and Inference schemas *)
      Construction.construction -> (* The construction to transform *)
      Construction.construction -> (* The goal to satisfy *)
      (Construction.construction list, Diagnostic.t list) Result.t (* Your new transformed structure graph :-) *)
end;

structure Transfer : TRANSFER =
struct

  type goal = Pattern.pattern
  exception TransferSchemaNotApplicable
  exception Error
  exception Err of string;


  fun firstUnusedName Ns =
        let fun mkFun n =
              let val vcandidate = "v_{"^(Int.toString n)^"}"
              in if FiniteSet.exists (fn x => x = vcandidate) Ns
                 then mkFun (n+1)
                 else vcandidate
              end
        in mkFun 0
        end
  (*  *)

  fun applyMorphismRefreshingNONEs given avoid CTs =
      let fun mkRenameFunction Ns Tks =
            let val (y,ys) = FiniteSet.pull Tks
                fun f x =
                  if CSpace.sameTokens x y
                  then SOME (CSpace.makeToken (firstUnusedName Ns) (CSpace.typeOfToken x))
                  else mkRenameFunction (CSpace.nameOfToken (Option.valOf (f y)) :: Ns) ys x
            in f
            end handle Empty => (fn _ => NONE)
          fun joinToks (x,y) = FiniteSet.union (Construction.tokensOfConstruction x) y
          val tokensInConstructions = foldl joinToks FiniteSet.empty CTs
          val names = FiniteSet.map CSpace.nameOfToken avoid
          fun renameFunction x =
              (case given x of
                  SOME y => SOME y
                | NONE => mkRenameFunction names tokensInConstructions x)
          val updatedConstructions = map (Pattern.applyMorphism renameFunction) CTs
      in (renameFunction, updatedConstructions)
      end

  (*  *)
  fun refreshNamesOfConstruction ct avoid =
    (case applyMorphismRefreshingNONEs (fn _ => NONE) avoid [ct] of
        (f,[x]) => (f,x)
      | _ => raise Error)


  exception InferenceSchemaNotApplicable
  fun applyInferenceSchemaForGoal st T idT ct ischData goal =
  let val {name,contextConSpecN,idConSpecN,iSchema,strength} = ischData
      val {antecedent,consequent,context} = iSchema
      fun referenced x =
        FiniteSet.elementOf x (Construction.tokensOfConstruction context) orelse
        FiniteSet.exists (fn y => FiniteSet.elementOf x (Construction.tokensOfConstruction y)) antecedent
      val givenTokens = FiniteSet.filter referenced (Construction.tokensOfConstruction consequent)

      val (consequentMap, updatedConsequent) =
          (case Pattern.findEmbeddingUpTo idT givenTokens consequent goal of
                (f,_,SOME x) => (f,x)
              | _ => raise InferenceSchemaNotApplicable)

      val (contextMap, matchingSubConstruction) =
            (case Seq.pull (Pattern.findEmbeddingsOfSubConstructionWithCompatibleInverse T ct context consequentMap) of
                SOME ((_,f,_,x),_) => (f,x)
              | _ => raise InferenceSchemaNotApplicable)

      val usedTokens = FiniteSet.union
                          (State.tokensInUse st)
                          (Pattern.tokensOfConstruction updatedConsequent)
      val ccMap = Pattern.funUnion CSpace.sameTokens [consequentMap, contextMap]
      val (_,updatedAntecedent) = applyMorphismRefreshingNONEs ccMap usedTokens antecedent

      val goals = State.goalsOf st
      val updatedGoals = List.merge Pattern.compare
                                    updatedAntecedent
                                    (List.filter (fn x => not (Pattern.same goal x)) goals)

      val instantiatedISchema = {antecedent = updatedAntecedent,
                                 consequent = updatedConsequent,
                                 context = matchingSubConstruction}
      val instantiatedISchemaData = {name = name,
                                     contextConSpecN = contextConSpecN,
                                     idConSpecN = idConSpecN,
                                     iSchema = instantiatedISchema,
                                     strength = strength}
      val transferProof = State.transferProofOf st
      val updatedTransferProof = TransferProof.attachISchemaAt instantiatedISchemaData goal transferProof

      val updatedState = State.updateTransferProof updatedTransferProof (State.updateGoals updatedGoals st)
  in updatedState
  end handle Pattern.IllDefined => raise InferenceSchemaNotApplicable

  (* The following function takes a tSchema, tsch, and a goal assumed to be
     matched by the consequent of tsch (up to the tokens of the original construction).
     The function will try to find a generator in the given source construction that matches
     the source pattern of tsch. If found, it will use the isomorphic map (from pattern to generator)
     to rename the relationships between the vertices of the source specified by the tSchema.
     It will also rename the vertices of the target pattern so that they don't clash with the
     vertices in the composition.  *)
  fun instantiateTransferSchema st tsch goal =
    let
      val {antecedent,consequent,source,target} = tsch

      val patternComps = State.patternCompsOf st
      val targetTokens = FiniteSet.intersection (Pattern.tokensOfConstruction goal)
                                                (Composition.tokensOfCompositions patternComps)
      val tTSD = State.targetTypeSystemOf st
      val tT = #typeSystem tTSD

      val ct = State.constructionOf st
      val T = #typeSystem (State.sourceTypeSystemOf st)
      val interTSD = State.interTypeSystemOf st
      val sourceConSpecData = #sourceConSpecData st
      val targetConSpecData = #targetConSpecData st
      val interConSpecData = #interConSpecData st

      fun preferentialFunUnion f g x = (case g x of NONE => f x | SOME y => SOME y)
      fun partialFunComp1 f g x = (case g x of NONE => f x | SOME y => f y)
      fun partialFunComp2 f g x = (case g x of NONE => f x
                                             | SOME y => (case f y of NONE => SOME y
                                                                    | SOME z => SOME z))
      fun funComp f g x = (case g x of NONE => NONE | SOME y => f y)

      fun referenced x =
          not (Type.isTypeVar (CSpace.typeOfToken x)) andalso
          (FiniteSet.elementOf x (Construction.tokensOfConstruction source) orelse
           FiniteSet.elementOf x (Construction.tokensOfConstruction target) orelse
           FiniteSet.elementOf x (FiniteSet.maps Construction.tokensOfConstruction antecedent))

      val givenTokens = FiniteSet.filter referenced (Construction.tokensOfConstruction consequent)

      val (consequentMap,goalMap,typeVarMap,newgoal) =
            (case Pattern.findEmbeddingMinimisingTypeUpTo interTSD givenTokens consequent goal of
                (f,g,vf,SOME ng) => (f,g,vf,ng)
              | _ => raise TransferSchemaNotApplicable)
      (*val _ = if Pattern.wellFormed interConSpecData newgoal then () else raise TransferSchemaNotApplicable*)
      val source = Pattern.applyTypeVarInstantiation typeVarMap source
      (*val _ = if Pattern.wellFormed sourceConSpecData source then () else raise TransferSchemaNotApplicable*)
      val target = Pattern.applyTypeVarInstantiation typeVarMap target
      (*val _ = if Pattern.wellFormed targetConSpecData target then () else raise TransferSchemaNotApplicable*)
      val antecedent = map (Pattern.applyTypeVarInstantiation typeVarMap) antecedent
      (*val _ = if List.all (Pattern.wellFormed interConSpecData) antecedent then () else raise TransferSchemaNotApplicable*)
      fun updateCMap [] = consequentMap
        | updateCMap (tk::tks) =
        let val f' = updateCMap tks
        in fn x => (case (typeVarMap (CSpace.typeOfToken tk), consequentMap tk) of
                        (SOME ityp, mtk) => (if Type.equal (CSpace.typeOfToken x) ityp andalso CSpace.nameOfToken tk = CSpace.nameOfToken x then mtk else f' x)
                      | _ => f' x)
        end
      val consequentMap = updateCMap (Construction.tokensOfConstruction consequent)

      val targetConstruct = Pattern.constructOf target
      val usedTokenNames = map CSpace.nameOfToken (State.tokensInUse st)
      val freshName = firstUnusedName usedTokenNames

      fun makeAttachmentToken tt =
          CSpace.makeToken freshName
                           (valOf (Type.greatestCommonSubType tTSD (CSpace.typeOfToken tt) (CSpace.typeOfToken targetConstruct)))
                           handle Option => raise TransferSchemaNotApplicable
      val newTargetConstruct =
          if FiniteSet.isEmpty targetTokens
          then CSpace.makeToken freshName (CSpace.typeOfToken targetConstruct)
          else (case FiniteSet.pull targetTokens of (tt,H) =>
                  if FiniteSet.isEmpty H
                  then makeAttachmentToken tt
                  else raise TransferSchemaNotApplicable
                )

      val usedTokens = FiniteSet.insert newTargetConstruct (State.tokensInUse st)
      fun targetConstructMap x =
        if CSpace.sameTokens x targetConstruct
        then SOME newTargetConstruct
        else NONE

      val (sourceMap, consVarMap, matchingSubConstruction) =
            (case Seq.pull (Pattern.findEmbeddingsOfSubConstructionWithCompatibleInverse T ct source consequentMap) of
                SOME ((_,f,cf,x),_) => (f,cf,x)
              | _ => raise TransferSchemaNotApplicable)

      val target = Pattern.applyConsVarInstantiation consVarMap target

      val updatedConsequent = Pattern.applyMorphism consequentMap consequent
      val csMap = Pattern.funUnion CSpace.sameTokens [sourceMap, consequentMap]
      val usedTokensC = FiniteSet.union usedTokens (Pattern.tokensOfConstruction updatedConsequent)

      fun getTargetEmbedding [] = NONE
        | getTargetEmbedding (tct::L) =
          (case Seq.pull (Pattern.findEmbeddingsOfSubConstructionWithCompatibleInverse tT tct target csMap) of
              SOME ((_,f,_,x),_) => SOME (f, x)
            | _ => getTargetEmbedding L)
      val targetConstructions = List.maps Composition.resultingConstructions patternComps
      val (targetReifiedByComposition,targetMap,updatedTarget) =
        (case getTargetEmbedding targetConstructions of
            SOME (f,_) =>
              let val tmap = preferentialFunUnion f targetConstructMap
              in (true,tmap,Pattern.applyMorphism tmap target)
              end
          | NONE =>
              let val (f,_) = applyMorphismRefreshingNONEs csMap usedTokensC [target]
                  val tmap = preferentialFunUnion f targetConstructMap
              in (false,tmap, Pattern.applyMorphism tmap target)
              end)

      fun compositionMap x = if FiniteSet.elementOf x targetTokens then SOME newTargetConstruct else NONE

      val cstMap = preferentialFunUnion csMap targetMap
      val usedTokensCT = FiniteSet.union usedTokensC (Construction.tokensOfConstruction updatedTarget)

      val (_,updatedAntecedent) = applyMorphismRefreshingNONEs cstMap usedTokensCT antecedent
    in
      (targetReifiedByComposition,
       preferentialFunUnion goalMap compositionMap,
       InterCSpace.declareTransferSchema {source = matchingSubConstruction,
                                          target = updatedTarget,
                                          antecedent = updatedAntecedent,
                                          consequent = updatedConsequent})
    end


  fun applyTransferSchemaForGoal st tschData goal =
    let val {name,sourceConSpecN,targetConSpecN,interConSpecN,tSchema,strength} = tschData
        val (targetReifiedByComposition,stateRenaming,instantiatedTSchema) = instantiateTransferSchema st tSchema goal

        val patternComps = State.patternCompsOf st
        val renamedPatternComps = map (Composition.applyPartialMorphism stateRenaming) patternComps
        val updatedPatternComps = if targetReifiedByComposition then renamedPatternComps else
            Composition.attachConstructions renamedPatternComps [#target instantiatedTSchema]

        val goals = State.goalsOf st
        val updatedGoals = List.merge Pattern.compare
                                      (#antecedent instantiatedTSchema)
                                      (map (Pattern.applyPartialMorphism stateRenaming) (List.filter (fn x => not (Pattern.same goal x)) goals))

        val instantiatedTSchemaData = {name = name,
                                        sourceConSpecN = sourceConSpecN,
                                        targetConSpecN = targetConSpecN,
                                        interConSpecN = interConSpecN,
                                        tSchema = instantiatedTSchema,
                                        strength = strength}
        val transferProof = State.transferProofOf st
        val updatedTransferProof = TransferProof.attachTSchemaAt instantiatedTSchemaData goal transferProof

        val updatedState = State.applyPartialMorphismToProof stateRenaming
                              (State.updateTransferProof updatedTransferProof
                                  (State.updateGoals updatedGoals
                                      (State.updatePatternComps updatedPatternComps st)))
    in updatedState
    end

  fun idempotencyOnGoals st =
    let fun rg (g::gs) =
            let val (keep,dump) = rg gs
            in if List.exists (Construction.same g) keep
               then (keep,g::dump)
               else (g::keep,dump)
            end
          | rg [] = ([],[])
        fun updateTransferProof (g::gs) = TransferProof.dump "idempotency" g (updateTransferProof gs)
          | updateTransferProof [] = State.transferProofOf st
        val (keep,dump) = rg (State.goalsOf st)
        val stateWithUpdatedGoals = State.updateGoals keep st
    in State.updateTransferProof (updateTransferProof dump) stateWithUpdatedGoals
    end

  fun applyTransferSchema st tschData =
    let val newSt = idempotencyOnGoals st
        val ct = State.constructionOf st
        fun ac [] = Seq.empty
          | ac (g::gs) = Seq.cons (applyTransferSchemaForGoal newSt tschData g) (ac gs)
                          handle TransferSchemaNotApplicable => ac gs
    in ac (State.goalsOf newSt)
    end

  fun applyInferenceSchema st ischData =
    let val newSt = idempotencyOnGoals st
        val ct = State.constructionOf newSt
        val T = #typeSystem (State.targetTypeSystemOf newSt)
        val idT = #typeSystem (State.interTypeSystemOf newSt)
        val pcts = List.maps Composition.resultingConstructions (State.patternCompsOf newSt)
        fun appToTargetConstructions [] _ = Seq.empty
          | appToTargetConstructions (h::L) g =
              (Seq.single (applyInferenceSchemaForGoal newSt T idT h ischData g))
                handle InferenceSchemaNotApplicable => appToTargetConstructions L g
        fun ac [] = Seq.empty
          | ac (g::gs) =
              (Seq.append (appToTargetConstructions pcts g) (ac gs))
                handle InferenceSchemaNotApplicable => (ac gs)
    in ac (State.goalsOf newSt)
    end

  fun singleStepTransfer st =
    let val tschs = Knowledge.transferSchemasOf (State.knowledgeOf st)
    in Seq.maps (applyTransferSchema st) tschs
    end

  fun singleStepInference st =
    let val ischs = Knowledge.inferenceSchemasOf (State.knowledgeOf st)
    in Seq.maps (applyInferenceSchema st) ischs
    end

  val transferElseInfer =  Seq.ORELSE (singleStepTransfer,singleStepInference)

  fun structureTransferTac h ign forget stop state =
      (*Search.breadthFirstIgnore transferElseInfer ign state*)
      (*Search.breadthFirstIgnoreForget transferElseInfer ign forget state*)
      (*Search.depthFirstIgnore transferElseInfer ign state*)
      (*Search.depthFirstIgnoreForget transferElseInfer ign forget state*)
      (*Search.bestFirstIgnore transferElseInfer h ign state*)
      (*Search.bestFirstIgnoreForget transferElseInfer h ign forget state*)
      Search.bestFirstAll transferElseInfer h ign forget stop state

  fun quickTransferTac ign forget stop state =
      Search.depthFirstIgnore transferElseInfer ign stop state

  exception Nope

  fun constructionOfComp st =
    (case List.maps Composition.resultingConstructions (State.patternCompsOf st) of
        [c] => c
      | _ => raise Nope)
      
  fun withinTarget targetTypeSystem targetPattern st =
    (Pattern.hasUnifiableGenerator targetTypeSystem targetPattern (constructionOfComp st))
      handle Nope => false

  fun matchesTarget targetTypeSystem targetPattern st =
    (Pattern.matches targetTypeSystem (constructionOfComp st) targetPattern)
      handle Nope => false    

(*splits TKW and checks if source patters matches any of its rules  [this is for the speedup instead of checking all states...] *)

  fun splitKnowledge con =
    case con of
            Construction.TCPair({token, constructor =(a,  b)}, [x, Construction.Source(name, "and"), rest]) =>  (x :: (splitKnowledge rest))
          | e => [e]

fun matchesTargetKw targetTypeSystem targetPattern st =
  List.exists (Pattern.hasUnifiableGenerator targetTypeSystem (constructionOfComp st)) (splitKnowledge targetPattern)
    handle Nope => false   

fun dropOpt (NONE::xs) = (dropOpt xs)
  | dropOpt (SOME(x)::xs) = (x :: dropOpt xs)
  | dropOpt [] = [];

fun afterSep ch [] = []
      | afterSep ch (x::xs) = if x = ch then xs else afterSep ch (xs);
      
fun dropType str = if not (Char.contains str #":") then str else String.implode (afterSep #":" (String.explode str))

fun propType (stri,stri2) = (dropType stri, dropType stri2) 

fun first  (f,s) = f;
fun second (f,s) = s;

fun unzip list = (List.map first list, List.map second list)

fun zip xs ys = ListPair.zipEq (xs,ys)
(*let val debug = print("before ZIp Match\n") in
  case (xs,ys) of
    ([],[]) => []
  | ((x::xs),(y::ys)) => ((x,y) :: (zip (xs) (ys)))
  | (_,_) => raise Err("zip") end*)

fun zipCon l1 cons = 
case cons of 
  [] => []
  |(x::xs) => ((l1, x)::(zipCon l1 xs))

fun exist s [] = false
  | exist s (x::xs) = (s = x) orelse exist s xs


fun exists s [] = false
  | exists s (x::xs) = (first s = first x andalso second x = second s) orelse exists s xs

(*fun isolate [] = []
  | isolate [NONE] = []
  | isolate (NONE::xs) = isolate xs
  | isolate (x::xs) = if exists x xs then xs else (x::xs)*)

fun isolateT [] = []
  | isolateT (x::xs) = if exists x xs orelse (first x = "_") orelse (first x = "formula") orelse (first x = "forall") orelse (first x = "and") orelse (first x = "not") orelse (first x = "forall") orelse (first x = "implies") then (isolateT xs) else (x :: isolateT xs);

(*fun sanitize emb =  isolateT (dropOpt (List.concat emb))*)

(*fun removeNone list = List.filter (fn y => y <> (NONE,NONE)) list;*)

fun third (x,y,z) = z;

fun printMap res [] = let val debug = print("THIS WAS THE LAST FOUND ANALOGY MAPPING\n======================\n")  in res end
  |  printMap res ((x,y)::xs) = 
    let val out =print("ANALOGY FOUND "^x^"->"^y^"\n") in printMap res xs 
    end;

fun disagreement [] = []
  | disagreement (x::xs) = if exist (first x) (List.map first xs) then disagreement xs else (x)::disagreement xs

fun agreeEmbeddings res list= 
let val candidates =  isolateT (List.concat list) 
    val debug = print("I'm agreeing embeddings...\n")
    (*val analogies = candidates in*)
    val analogies = disagreement (isolateT (List.map propType candidates)) in 
printMap res analogies end;

fun inLookup s lk =
case lk of 
[] => false
| ((x,y)::xs) => if first y = s then true else  inLookup s xs

fun findLk s lk =
case lk of 
[] => raise Err("no lookup")
| ((x,y)::xs) => if first y = s then (second x) else findLk s xs 

 fun crawl (lookup, embPatt) = 
  let fun change (stype, ttype) = ((findLk (first stype) lookup), ttype)
  in 
  case embPatt of 
   Construction.TCPair(smth, cl) => 
   let val consZip = (zipCon lookup cl) in
    List.concat (List.map crawl consZip) end
  | Construction.Source(tok, smth) =>  if inLookup tok lookup then [change ((tok, smth), smth)] else [("_" , smth)] (*this might be iffy*)
  end

fun crawlWrap (embPatt, lk) = 
case (embPatt, lk) of 
(embPattt, lkk) => crawl (lkk,embPattt)
| (_,_) => [("","")]

(**)
fun firstTwo (x::y::xs) = (x,y) 
    | firstTwo (x::[]) = (x,x)
    | firstTwo [] = raise Err("fTwo")
  
fun structureTransfer (goalLimit,compositionLimit,searchLimit) eager unistructured targetPattOption st =
  let val maxNumGoals = case goalLimit of SOME x => x | NONE => 80
      val maxCompSize = case compositionLimit of SOME x => x | NONE => 300
      val maxNumResults = case searchLimit of SOME x => x | NONE => 1000
      val ignT = Heuristic.ignore maxNumGoals maxNumResults maxCompSize unistructured
       val targetTypeSystem = #typeSystem (State.targetTypeSystemOf st)
      fun ignPT (x,L) = case targetPattOption of
                      SOME tpt => not (matchesTargetKw targetTypeSystem tpt x) orelse ignT (x,L) 
                    | NONE => ignT (x,L)
      fun fgtPT (x,L) = case targetPattOption of
                      SOME tpt => not (matchesTargetKw targetTypeSystem tpt x) (*(*CHANGED HERE from matchesTarget to matchesTargetKw*)
                                  Heuristic.forgetRelaxed (x,L)*)
                    | NONE => false (*Heuristic.forgetRelaxed (x,L)*)
      val stop = if eager then (fn x => null (State.goalsOf x)) else (fn _ => false)
      val tac = structureTransferTac Heuristic.transferProofMain ignPT fgtPT stop
  in tac st
  end


fun analogyTransfer (goalLimit,compositionLimit,searchLimit) eager unistructured targetPattOption st =
  let val maxNumGoals = case goalLimit of SOME x => x | NONE => 80
      val maxCompSize = case compositionLimit of SOME x => x | NONE => 300
      val maxNumResults = case searchLimit of SOME x => x | NONE => 1000
      val ignT = Heuristic.ignore maxNumGoals maxNumResults maxCompSize unistructured
      val debug = case targetPattOption of SOME tpt => print("TARGET PATTERN:\n" ^ (Construction.toString tpt)^"\n") |NONE => print(";\n")
      val targetTypeSystem = #typeSystem (State.targetTypeSystemOf st)
      fun ignPT (x,L) = case targetPattOption of
                      SOME tpt => not (matchesTargetKw targetTypeSystem tpt x) orelse ignT (x,L) 
                    | NONE => ignT (x,L)
      fun fgtPT (x,L) = case targetPattOption of
                      SOME tpt => not (matchesTargetKw targetTypeSystem tpt x) (*(*CHANGED HERE from matchesTarget to matchesTargetKw*)
                                  Heuristic.forgetRelaxed (x,L)*)
                    | NONE => false (*Heuristic.forgetRelaxed (x,L)*)
      val stop = if eager then (fn x => null (State.goalsOf x)) else (fn _ => false)
      val tac = structureTransferTac Heuristic.transferProofMain ignPT fgtPT stop
  in tac st
  end

fun take3 list = List.take (list, 3)

fun embeddingPartial TS target ([rule], lookup) = 
let val no = List.find (fn x => third (Pattern.findEmbedding TS rule x) <> NONE) (splitKnowledge target (*[target]*)) in
if no <> NONE then
(let val SOME(nom) = no
      val (f1, f2, SOME(patt)) = Pattern.findEmbedding TS rule nom in SOME(patt, lookup) end) else NONE end
      | embeddingPartial TS target (rule, lookup) = let val debug = PolyML.print rule in raise Err("degenerated result") end

(*List.mapPartal (fn x => x)
  
fun zipRsLk res lk =
case (res, lk) of
(x::xs, [y]::ys) => (((x,y)) :: zipRsLk x ys)
| ([],[]) => []*)

fun zipNested (res, lk) = ListPair.map (ListPair.zipEq) (res,lk) (*ListPair.Map*)


(*val debug = print(Construction.toString List.hd (List.hd embeddignsPartial))*)
(*val debug = print(Construction.toString target)*)
(*val debug = print(Construction.toString List.hd (splitKnowledge target))*)
(*val debug = print(Construction.toString (List.hd (List.hd results)))*)
fun analogySearch limits eager unistructured targetPatt st  =
let val source = State.constructionOf st
    val target = targetPatt
    val tTypS = #typeSystem (State.targetTypeSystemOf st)
    val debug = PolyML.print_depth 20
    (*transfer on split rules
    val debug = PolyML.print source*)
    val rulesToMatch = splitKnowledge source 
    (* val debug = print("\nfirst rule in source is "^(Construction.toString (List.hd rulesToMatch))^"\n")
    val debug = PolyML.print List.hd rulesToMatch*)
    val debug = print("wait for big transfer to run...\n") 
    val res = (structureTransfer limits eager unistructured NONE st)
    val debug = print("got through big transfer;\n") 
    (*val debug = if Construction.same source (List.hd rulesToMatch) then print("WHAT THE F") else raise Err("Different")*)
    val splitStates = List.map (State.updateConstruction st) rulesToMatch 
     (*val debug = PolyML.print (List.hd splitStates)
    val debug = PolyML.print (st)
    val debug = print("Found this many source rules:\n"^(Int.toString(List.length splitStates)))*)
    val debug = print("\ngot through split states;\n") 
    val transferSeq = List.map (structureTransfer limits eager unistructured NONE) splitStates (*list of sequences of states for each rule*)
    (*val debug = print("Found this many transferred  Sequences:\n"^(Int.toString(List.length transferSeq)))*)
    val debug = print("got through each rule transfer, first is:\n") 
    val transferred = List.map Seq.list_of transferSeq (*State.T list list*)
    val debug = print("This many rules got tranferred:\n"^(Int.toString (List.length (List.hd transferred))))
    val debug = print("First rule has this many seq results:\n"^(Int.toString (List.length (List.hd transferred))))
    (*val debug = print("and now mine:\n") 
    val debug = PolyML.print (transferred)*)
    val debug = print("turned into transfers list of lists;\n") 
    val compsList = List.map (List.map State.patternCompsOf) transferred (*this can fold into results later*)
    (*val debug = PolyML.print compsList*)
    val results =  List.map (List.map (List.map (List.hd o Composition.resultingConstructions))) compsList
    val debug = print("number of results' rules: "^(Int.toString (List.length (results)))) (* ^"\nAnd the results, in a list for each rule\n:")
   val debug = PolyML.print results*)
     val debug = print("extracted results;\n") 
    (*create lookups*)
    val goals = List.map (List.map State.goalsOf) transferred 
    val pairs = List.map (List.map (List.map Construction.leavesOfConstruction)) goals
    (*val debug = PolyML.print pairs*)
    val lookup = List.map (List.map (List.map firstTwo)) pairs
    val debug = print("extracted lookup for those;\n") 
    val debug = PolyML.print lookup
    (*val debug = print(results)*)
    val debug = print("created lookups;\n")
    (*embedd*)
    (*val toEmbed = List.map (ListPair.map (ListPair.zip)) (results,lookup)*)
    val toEmbed = ListPair.map (ListPair.zipEq) (results, lookup)
    (*val debug = PolyML.print toEmbed*)
    (*val debug = print (toEmbed)*)
    (*val debug = print("type sys tar:\n")
    val debug = PolyML.print (#name (State.targetTypeSystemOf st))*)
    val embeddingsOpt = List.map (List.map (embeddingPartial tTypS target)) toEmbed
    val embeddings = List.map (List.mapPartial (fn x => x)) embeddingsOpt
    val debug = print("extracted embeddings;\n") 
    (*val debug = PolyML.print (List.length embeddings)*)
    val debug = PolyML.print embeddings
    (*val maps = List.map (List.mapPartial second) (embeddings) *)
    val crawlMap = List.map (crawlWrap)
    val STembeddings = List.map crawlMap (embeddings)
    val debug = print("list of embedding pairs:\n") 
    val debug = PolyML.print STembeddings
    val debug = print("crawled through;\n") 
    val intro = print("\n======================\n ANALOGY MAPPINGS FOUND:\n")
  in 
  agreeEmbeddings res (List.concat STembeddings) (*in res *)end;


  fun quickTransfer (goalLimit,compositionLimit,searchLimit) unistructured targetPattOption st =
    let val maxNumGoals = case goalLimit of SOME x => x | NONE => 15
        val maxCompSize = case compositionLimit of SOME x => x | NONE => 200
        val maxNumResults = case searchLimit of SOME x => x | NONE => 1000
        val ignT = Heuristic.ignore maxNumGoals maxNumResults maxCompSize unistructured
        val targetTypeSystem = #typeSystem (State.targetTypeSystemOf st)
        fun ignPT (x,L) = case targetPattOption of
                        SOME tpt => not (withinTarget targetTypeSystem tpt x) orelse ignT (x,L)
                      | NONE => ignT (x,L)
        fun fgtPT (x,L) = case targetPattOption of
                        SOME tpt => not (matchesTarget targetTypeSystem tpt x) (*orelse
                                    Heuristic.forgetRelaxed (x,L)*)
                      | NONE => false (*Heuristic.forgetRelaxed (x,L)*)
        val stop = (fn x => null (State.goalsOf x))
        val tac = quickTransferTac ignPT fgtPT stop
    in tac st
    end

  fun v2t t =
    let val tok = CSpace.nameOfToken t
        val typ = CSpace.typeOfToken t
        fun vt (x::xs) = if x = #"v" then #"t"::xs else x::xs
          | vt [] = []
    in SOME (CSpace.makeToken (String.implode (vt (String.explode tok))) typ)
    end

(*
   TODO : recoding an iterative structure transfer would be nice
*)

fun masterTransfer limits eager iterative unistructured targetPattOption st =
    (*structureTransfer limits eager unistructured targetPattOption st*)
    case targetPattOption of 
    NONE => structureTransfer limits eager unistructured targetPattOption st
    | SOME(target) => analogySearch limits eager unistructured target st

  fun initState sCSD tCSD iCSD inverse KB ct goal =
    let val tTS = #typeSystem (#typeSystemData tCSD)
        val targetTokens = FiniteSet.filter
                               (fn x => Set.elementOf (CSpace.typeOfToken x) (#Ty tTS) andalso
                                        not (FiniteSet.elementOf x (Construction.tokensOfConstruction ct)))
                               (Construction.leavesOfConstruction goal);
    in State.make {sourceConSpecData = sCSD,
                   targetConSpecData = tCSD,
                   interConSpecData = iCSD,
                   transferProof = TransferProof.ofPattern goal,
                   construction = ct,
                   originalGoal = goal,
                   goals = [goal],
                   compositions = map Composition.makePlaceholderComposition targetTokens,
                   knowledge = Knowledge.filterForISpace (#name iCSD) inverse KB}
    end

  fun applyTransfer sCSD tCSD iCSD KB ct goal =
      let val st = initState sCSD tCSD iCSD false KB ct goal
          val stateSeq = structureTransfer (SOME 6,NONE,NONE) true false NONE st;
          fun getStructureGraph st =
              List.flatmap Composition.resultingConstructions (State.patternCompsOf st);
          fun makeDiagnostic goal =
              let val str = Construction.toString goal;
                  val toks = FiniteSet.listOf
                                 (Construction.tokensOfConstruction goal);
                  fun hexDigit c = Char.contains "0123456789ABCDEFabcdef" c;
                  fun couldBeId [] = false
                    | couldBeId [c] = hexDigit c
                    | couldBeId (c::cs) = if c = #"-" orelse hexDigit c
                                          then List.all hexDigit cs
                                          else false;
                  fun asId s = if couldBeId (String.explode s) then SOME s else NONE;
                  val ids = List.mapPartial (asId o CSpace.nameOfToken) toks;
              in Diagnostic.create
                     Diagnostic.ERROR
                     ("Transfer failed due to open goal: " ^ str)
                     ids
              end;
          val firstState = Seq.hd stateSeq;
          val goals = State.goalsOf firstState;
      in case goals of
             [] => Result.ok (getStructureGraph firstState)
           | _ => Result.error (List.map makeDiagnostic goals)
      end

  

  fun find pred [] = NONE
    | find pred (x::rest) = if pred x then SOME x else find pred rest;

  fun lookup(k,table) = 
  find (fn (key, value) => key = k) table

end;
