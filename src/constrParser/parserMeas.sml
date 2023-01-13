import "util.logging";
import "oruga.document";
import "core.construction";
import "core.pattern";
Logging.enable ();

(*  


run: 
import "constrParser.parserMeas";

val rule1 = Construction.toString (parserMeas.parseRule 0 (parserMeas.stripSpaces "V s1 V s2 L s1 s2 * S s2 s1"));

val rule2 = Construction.toString (parserMeas.parseRule 0 (parserMeas.stripSpaces "V s1 V s2 V s3 E s1 s2 s3* C s3 s2 s1"));

val rule3 = Construction.toString (parserMeas.parseRule 0 (parserMeas.stripSpaces "V s1 V s2 ~ S s1 s2 > ~ L s2 s1 > s1 = s2"));

val rule4 = Construction.toString (parserMeas.parseRule 0 (parserMeas.stripSpaces "V s1 ~ L u1 s1"));

val rule5 = Construction.toString (parserMeas.parseRule 0 (parserMeas.stripSpaces "V s1 V s2  S s1 s2 > ~ S s2 s1"));

val rule6 = Construction.toString (parserMeas.parseRule 0 (parserMeas.stripSpaces "V s1 V s2 V  s3 E s1 s2 s3 > L s3 s2 & L s3 s1"));

bigConstruction = parserMeas.joinAnds 1 [rule1, rule2, rule3, rule4, rule5]

val {conSpecsData, constructionsData, knowledge, strengths, transferRequests, typeSystemsData} = it;
[V s1 ~L U, S]
val [al, r6,r5,r4,r3,r2,r1] = constructionsData

parserMeas.joinAnds 1 [r1,r2,r3,r4,r5,r6];

val {conSpecN, construction, name} = r6;
val r6 = construction;


the semantics: ∀ x1-> V x1 | > -> implies | * -> <=> | A -> and between rules | & -> and within the rules | ~ -> not | shorter -> S | longer -> L | extend -> E | chop -> C
syntax is CONSTRUCTIONNAME | first rule A second rule A third rule for example:"
parseinput ''ThreeRulesTogether | [Vs1| Vs2 (s |s1|, |s2| = l |s2|, |s1| * s |s1| |s2| = |s2| |s1|)] A [second rule] A [third rule]nger s2, s1)] A [second rule] A [third rule]''] 0" 
the order of splitting within rules is: quants > equivalence/implies > = > and > not >  predicates"*)


(*Construction.TCPair ({token = token, constructor = constructor}, cs)*
  datatype construction = Construction.TCPair of {token : string * string,
                                     constructor : string * (string list * string)} 
                                    * construction list
                        | Construction.Source of string * string (ownname, generic)
                        | Reference of string * string (ownname, generic)
*)
signature PARSERMEAS =
sig 
    val StringParseError : string -> exn;
    val splitRules: char -> char list -> string list;
    val beforeSep: char -> char list -> char list -> char list
    val afterSep: char -> char list -> char list
    val reverse: 'a list -> 'a list
    val exists: char list -> char ->  bool
    val joinAnds: int -> Construction.construction list -> Construction.construction
    val parseRule: int -> string -> Construction.construction
    val stripSpaces: string -> string
    (* val inputIntoConstructionData: string -> Cspace.cons*)
    val stringIntoConstruction: string -> Construction.construction
end;


structure parserMeas : PARSERMEAS =
  struct
    exception StringParseError of string;
    exception CodeError;

  fun splitRules sep L =
      let
        fun sl _ [] = [[]]
          | sl (p,s,c) (x::xs) =
              let val p' = if x = #"(" then p+1 else (if x = #")" then p-1 else p)
                  val s' = if x = #"[" then s+1 else (if x = #"]" then s-1 else s)
                  val c' = if x = #"{" then c+1 else (if x = #"}" then c-1 else c)
                  val slr = sl (p',s',c') xs
              in
                if (p',s',c') = (0,0,0) then if x = sep then []::slr
                                              else (case slr of
                                                      (L::LL) => (x::L) :: LL
                                                    | _ => raise CodeError)
                else (case slr of (L::LL) => (x::L) :: LL | _ => raise CodeError)
              end
        in List.map (String.implode) (sl (0,0,0) L)
      end
    (* parseRule takes in string to parse and accumulator construction (whatever was already parsed) and recursively moves things from string to acc in order from above";

    joinAnds takes in list of rules to turn into construction of ands;*)

  fun joinAnds d [] = raise StringParseError("No rules found. Did you forget '[]'s?")
    | joinAnds d (x :: []) = x
    | joinAnds d (x :: y) =
          let val rest = joinAnds (d) y in
          Construction.TCPair({constructor = ("logicInfixOp", (["formula", "binary", "formula"], "formula")), token  = ("rule" ^ (Int.toString d) ^"andrest", "formula")}, 
              [x, Construction.Source("A"^(Int.toString d), "and"), rest])
          end

  fun exists [] x = false
    | exists (y::ys) x = (x = y) orelse exists ys x
  
  fun beforeSep ch [] acc = acc
      | beforeSep ch (x::xs) acc = if x = ch then acc else if x = #"(" then (beforeSep ch xs []) else (beforeSep ch xs (acc @ [x]))

    fun afterSep ch [] = []
      | afterSep ch (x::xs) = if x = ch  then xs else if x = #")" then xs else x::afterSep ch (xs)
  

  fun SafterSepS ch str = String.implode (afterSep ch (String.explode str))

  fun SbeforeSepS ch str = String.implode (beforeSep ch (String.explode str) [])

  fun reverse nil = nil | reverse (x::xs) = (reverse xs) @ [x]

  fun stringToConstruct [] l = ""
    |stringToConstruct (y::ys) 0 = String.implode ys
    |stringToConstruct (y::ys) l = stringToConstruct ys (l-1)

  fun parseRule d stri =
    let val str = (String.explode stri) in
      if exists str #"V" then Construction.TCPair({constructor = ("logicApplyQuant", (["forall", "seg", "formula"], "formula")), token =("t"^Int.toString d, "formula")},
                          [Construction.Source ("q"^Int.toString d, "forall"), Construction.Source (String.substring (stri, 1,2), "seg"), parseRule (d+1) (String.extract (stri, 3, NONE))])
      else if exists str #">" then
                          let val left = SbeforeSepS #">" stri 
                           val right = SafterSepS #">" stri in
                          Construction.TCPair({constructor = ("logicInfixOp", (["formula", "implies", "formula"], "formula")), token =("timp"^Int.toString d, "formula")},
                          [parseRule (d+1) left, Construction.Source ("imp"^Int.toString d, "implies"), parseRule (d+1) right]) end
      else if exists str #"*" then 
                          let val left = SbeforeSepS #"*" stri 
                              val right = SafterSepS #"*" stri  in
                          Construction.TCPair({constructor = ("logicInfixOp", (["formula", "equiv", "formula"], "formula")), token =("teqv"^Int.toString d, "formula")}, 
                          [parseRule (d+1) left, Construction.Source ("equiv", "binary"), parseRule (d+1) right]) end
      else if exists str #"&" then 
                          let val left = SbeforeSepS #"&" stri
                              val right = SafterSepS #"&" stri in
                          Construction.TCPair({constructor = ("logicInfixOp", (["formula", "and", "formula"], "formula")), token =("tand"^Int.toString d, "formula")},
                          [parseRule (d+1) left, Construction.Source ("and"^Int.toString d, "and"), parseRule (d+1) right]) end
      else if exists str #"=" then 
                          let val left = SbeforeSepS #"=" stri
                              val right = SafterSepS #"=" stri in
                          Construction.TCPair({constructor = ("logicInfixOp", (["formula", "equals", "formula"], "formula")), token =("teq"^Int.toString d, "formula")}, 
                          [parseRule (d+1) left, Construction.Source ("eqs"^Int.toString d, "equals"), parseRule (d+1)  right])  end
      else if exists str #"~" then 
                          let val right = SafterSepS #"~" stri in
                          Construction.TCPair({constructor = ("logicUnPred", (["not", "obj"], "obj")), token =("tnot"^Int.toString d, "object")},
                          [Construction.Source ("nt"^Int.toString d, "not"), parseRule (d+1) right]) end 
      else if exists str #"S" then 
                          let val right = SafterSepS #"S" stri in
                          Construction.TCPair({constructor = ("prefixBinRel", (["prefixBinRel", "seg", "seg"], "formula")), token =("tshr"^Int.toString d, "formula")},[Construction.Source ("sh"^Int.toString d, "shorter"), Construction.Source (String.substring (right, 0,2), "seg"), Construction.Source (String.substring (right, 2,2), "seg")]) (*issue here*)  end 
      else if exists str #"L" then 
                          let val right = SafterSepS #"L" stri in
                          Construction.TCPair({constructor = ("prefixBinRel", (["prefixBinRel", "seg", "seg"], "formula")), token =("tlog"^Int.toString d, "formula")}, [Construction.Source ("lg"^Int.toString d, "longer"), Construction.Source(String.substring (right, 0,2), "seg"), Construction.Source (String.substring (right, 2,2), "seg")]) end 
      else if exists str #"E" then 
                          let val right = SafterSepS #"E" stri in
                          Construction.TCPair({constructor = ("prefixTerOp", (["prefixTerOp", "seg", "seg", "seg"], "seg")), token =("text"^Int.toString d, "formula")}, [Construction.Source ("exd"^Int.toString d, "extend"), Construction.Source(String.substring (right, 0,2), "seg"), Construction.Source (String.substring (right, 2,2), "seg"), Construction.Source(String.substring (right, 4,2), "seg")]) end
      else if exists str #"C" then 
                          let val right = SafterSepS #"C" stri in
                          Construction.TCPair({constructor = ("prefixTerOp", (["prefixTerOp", "seg", "seg", "seg"], "seg")), token =("tchp"^Int.toString d, "formula")}, [Construction.Source ("chop^Int.toString d", "chop"), Construction.Source(String.substring (right, 0,2), "seg"), Construction.Source(String.substring (right, 2,2), "seg"), Construction.Source(String.substring (right, 4,2), "seg")]) end
      (*the only left thing is a segment, which might have a name/token-type*)     
      else if String.isPrefix "|" stri then 
                Construction.Source ((SbeforeSepS #"|" stri), "seg")
      else  if String.size stri = 0 then raise StringParseError("TRIED TO PARSE EMPTY STRING") else Construction.Source("s"^Int.toString d, "seg") end

  fun noSpaceChL [] = []
    | noSpaceChL (x::xs) = if x = #" " then noSpaceChL xs else x::( noSpaceChL xs)

    fun stripSpaces stri =
    String.implode (noSpaceChL (String.explode stri))

 (*use String.extract*)
  fun stringIntoConstruction stri = 
      let val str = stripSpaces stri
         val construction = joinAnds 1 (List.map (parseRule 1) (splitRules #"A" (String.explode stri))) in
        construction
      end

end

  (*fun stringIntoConstructionData stri =
    let val str = String.stripSpaces stri
        val name = beforeSep #"|" (String.explode str) [] 
        val consSpecN = "measStickG" 
        val toConstruct = stringToConstruct(String.explode str) (String.size name) 
        val construction = joinAnds(List.map (parseRule 1) (splitRules (String.explode toConstruct))) 
        val constructionData = {name = name, conSpecN = conSpecN, construction = construction} in
    constructionData;
    end*) 