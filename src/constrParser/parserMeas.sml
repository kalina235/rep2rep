import "util.logging";
import "oruga.document";
import "core.construction";
import "core.pattern";
import "core.cspace";
Logging.enable ();

(*  
the semantics:
first 2 letters for each rule should be a rule identifier (so that tokens are unique between rules, then the rules translated according to:
∀ x1-> V x1 | > -> implies | * -> <=> | A -> and between rules | & -> and within the rules | ~ -> not | shorter -> S | longer -> L | extend -> E | chop -> C
the order of splitttwoing within rules is: quants > equivalence/implies > = > and > not >  predicates
each segment should have a 2 letter name (s#) unitSeg must be 2 letters and start with a u.
examples in constrParser/copypastes
*)

signature PARSERMEAS =
sig 
    val StringParseError : string -> exn;
    val splitRules: char -> char list -> string list; 
    val joinAnds: int -> Construction.construction list -> Construction.construction 
    val parseWrap: string -> string (*single rule into string*)
    val parse: string -> Construction.construction
    val stringIntoConstruction: string -> Construction.construction
    (*
    val fixUnit: Construction.construction -> Construction.construction <- this fixes unitSeg
    val exists: char list -> char ->  bool
    val stripSpaces: string -> string
    val inputIntoConstructionData: string -> Cspace.cons
    val parseRule: string -> int -> int -> string -> Construction.construction*)
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

  fun exists [] x = false
    | exists (y::ys) x = (x = y) orelse exists ys x
  
  fun beforeSep ch [] acc = acc
      | beforeSep ch (x::xs) acc = if x = ch then acc else if x = #"(" then (beforeSep ch xs []) else (beforeSep ch xs (acc @ [x]))

  fun afterSep ch [] = []
      | afterSep ch (x::xs) = if x = ch then xs else afterSep ch (xs);
      
  fun SafterSepS ch str = String.implode (afterSep ch (String.explode str))

  fun SbeforeSepS ch str = String.implode (beforeSep ch (String.explode str) [])

  fun reverse nil = nil | reverse (x::xs) = (reverse xs) @ [x]

  fun stringToConstruct [] l = ""
    |stringToConstruct (y::ys) 0 = String.implode ys
    |stringToConstruct (y::ys) l = stringToConstruct ys (l-1)

  (*fun listOfTokens conn =
        case conn of 
          Construction.TCPair({token, constructor}, cL) => (token :: ((List.map listOfTokens cL)))
        | Construction.Source(tok, typ) => [CSpace.token(tok)]
  fun findRepeatToken con =
    let fun findRepeatList (x::xs) = if exists xs x then (x :: (findRepeatList xs)) else findRepeatList xs
          | findRepeatList [] = []
      in 
        findRepeatList (listOfTokens con)
      end
  *)
  fun fixUnit conn = (*this is important. unitSeg is not subtypable!*)
    case conn of
      Construction.Source(token, typeName) => if String.substring(typeName, 0, 1) = "u" then  Construction.Source("u"^token, "unitSeg") else  Construction.Source(token, typeName)
    | Construction.TCPair(tc, cL) =>  Construction.TCPair(tc, List.map fixUnit cL)
    | Construction.Reference(tc) => raise StringParseError("You've got a loop in your construction")

  fun parseRule p branch depth stri =
      let 
        val str = (String.explode stri) (*will need list of Chars version*)
        val b = Int.toString branch (* need to distinguish branch and depth,*)
        val d = Int.toString depth  (* so that token names are unique [branch is pushed onto prefix]*)
        val p = p^b
      in    
      if exists str #"V" then Construction.TCPair({constructor = ("logicApplyQuant", (["forall", "obj", "formula"], "formula")), token =("tqnt"^p^d, "formula")},
                          [Construction.Source ("q"^p^d, "forall"), Construction.Source ("s"^p^d, String.substring (stri, 1,2)^":seg"), parseRule p 1 (depth+1) (String.extract (stri, 3, NONE))])
      else if exists str #">" then
                          let val left = SbeforeSepS #">" stri 
                              val right = SafterSepS #">" stri in
                          print(left^"  AND "^right^"\n"); Construction.TCPair({constructor = ("logicInfixOp", (["formula", "implies", "formula"], "formula")), token =("timp"^p^d, "formula")},
                          [parseRule p 1 (depth+1) left, Construction.Source ("imp"^p^d, "implies"), parseRule p 2 (depth+1) right]) end
      else if exists str #"*" then 
                          let val left = SbeforeSepS #"*" stri 
                              val right = SafterSepS #"*" stri  in
                          print(left^"  AND "^right^"\n"); Construction.TCPair({constructor = ("logicInfixOp", (["formula", "equiv", "formula"], "formula")), token =("teqv"^p^d, "formula")}, 
                          [parseRule p 1 (depth+1) left, Construction.Source ("eqv"^p^d, "equiv"), parseRule p 2 (depth+1) right]) end
      else if exists str #"v" then 
                          let val left = SbeforeSepS #"v" stri
                              val right = SafterSepS #"v" stri in
                          print(left^"  OR "^right^"\n"); Construction.TCPair({constructor = ("logicInfixOp", (["formula", "or", "formula"], "formula")), token =("tor"^p^d, "formula")},
                          [parseRule p 1 (depth+1) left, Construction.Source ("or"^p^d, "or"), parseRule p 2 (depth+1) right]) end
      else if exists str #"&" then 
                          let val left = SbeforeSepS #"&" stri
                              val right = SafterSepS #"&" stri in
                          print(left^"  AND "^right^"\n"); Construction.TCPair({constructor = ("logicInfixOp", (["formula", "and", "formula"], "formula")), token =("tand"^p^d, "formula")},
                          [parseRule p 1 (depth+1) left, Construction.Source ("and"^p^d, "and"), parseRule p 2 (depth+1) right]) end
      else if exists str #"~" then 
                          let val right = SafterSepS #"~" stri in
                          print(right^"\n");Construction.TCPair({constructor = ("logicApplyUnary", (["not", "formula"], "formula")), token =("tnot"^p^d, "formula")},
                          [Construction.Source ("nt"^p^d, "not"), parseRule p 1 (depth+1) right]) end 
      else if exists str #"=" then 
                          let val left = SbeforeSepS #"=" stri
                              val right = SafterSepS #"=" stri in
                          print(left^"  AND "^right^"\n"); Construction.TCPair({constructor = ("infixBinRel", (["obj", "equals", "obj"], "formula")), token =("teq"^p^d, "formula")}, 
                          [parseRule p 1 (depth+1) left, Construction.Source ("eqs"^p^d, "equals"), parseRule p 2 (depth+1)  right])  end
      else if exists str #"E" then 
                          let val right = SafterSepS #"E" stri in
                          print(right^"\n");Construction.TCPair({constructor = ("prefixTerRel", (["terRel", "obj", "obj", "obj"], "formula")), token =("text"^p^d, "formula")}, [Construction.Source ("exd"^p^d, "extend"), Construction.Source("s"^p^"1"^d, String.substring (right, 0,2)^":seg"), Construction.Source("s"^p^"2"^d, String.substring (right, 2,2)^":seg"), Construction.Source("s"^p^"3"^d, String.substring (right, 4,2)^":seg")]) end
      else if exists str #"C" then 
                          let val right = SafterSepS #"C" stri in
                          print(right^"\n");Construction.TCPair({constructor = ("prefixTerRel", (["terRel", "obj", "obj", "obj"], "formula")), token =("tchp"^p^d, "formula")}, [Construction.Source ("chp"^p^d, "chop"), Construction.Source("s"^p^"1"^d, String.substring (right, 0,2)^":seg"), Construction.Source("s"^p^"2"^d, String.substring (right, 2,2)^":seg"), Construction.Source("s"^p^"3"^d, String.substring (right, 4,2)^":seg")]) end
      else if exists str #"L" then 
                          let val right = SafterSepS #"L" stri in
                          print(right^"\n");Construction.TCPair({constructor = ("prefixBinRel", (["binRel", "obj", "obj"], "formula")), token =("tlog"^p^d, "formula")}, [Construction.Source ("lg"^p^d, "longer"), Construction.Source("s"^p^"1"^d, String.substring (right, 0,2)^":seg"), Construction.Source("s"^p^"2"^d, String.substring (right, 2,2)^":seg")]) end 
      else if exists str #"S" then 
                          let val right = SafterSepS #"S" stri in
                          print(right^"\n");Construction.TCPair({constructor = ("prefixBinRel", (["binRel", "obj", "obj"], "formula")), token =("tshr"^p^d, "formula")},[Construction.Source ("sh"^p^d, "shorter"), Construction.Source("s"^p^"1"^d, String.substring (right, 0,2)^":seg"), Construction.Source("s"^p^"2"^d, String.substring (right, 2,2)^":seg")]) (*issue here*)  end 
      else if String.size stri < 3  then 
                          Construction.Source ("CPs"^p^d, String.extract(stri, 0, NONE)^":seg")
      else  if String.size stri = 0 then raise StringParseError("TRIED TO PARSE EMPTY STRING") else Construction.Source("s"^p^d, "seg") end;


  fun stripSpaces stri =
    let fun noSpaceChL [] = []
          | noSpaceChL (x::xs) = if x = #" " then noSpaceChL xs else x::( noSpaceChL xs) 
        in
        String.implode (noSpaceChL (String.explode stri)) 
    end

  fun parse stri = fixUnit(parseRule (String.substring (stri, 0,2)) 1 1 (stripSpaces (String.extract (stri, 2, NONE))))

  fun parseWrap stri = Construction.toString (parse stri)

  fun joinAnds d [] = raise StringParseError("No rules found. Did you forget '[]'s?")
    | joinAnds d (x :: []) = x
    | joinAnds d (x :: y) =
          let val rest = joinAnds (d+1) y in
          Construction.TCPair({constructor = ("logicInfixOp", (["formula", "binary", "formula"], "formula")), token  = ("rule" ^ (Int.toString d) ^"andrest", "formula")}, 
              [x, Construction.Source("A"^(Int.toString d), "and"), rest])
          end

  fun stringIntoConstruction stri = 
    let val str = stripSpaces stri
        val construction = joinAnds 1 (List.map parse ( (splitRules #"A" (String.explode str)))) in
      construction
    end
(*)
  fun stringIntoConstructionData stri =
    let val str = String.stripSpaces stri
        val name = SbeforeSepS #"|" stri
        val consSpecN = "measStickG" 
        val construction = stringIntoConstruction (Space)
        val constructionData = {name = name, conSpecN = conSpecN, construction = construction} in
    constructionData;
    end*)
end