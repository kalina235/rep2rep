import "transfer.structure_transfer";
import "util.logging";
import "transfer.propagation";
import "input.measStick";
Logging.enable ();


val comment1 = "the semantics: ∀ x1-> V x1| | > -> implies | * -> <=> | A -> and between rules | & -> and within the rules | ~ -> not | shorter -> s | nameoftoken -> nameoftoken|"
val comment2 = "syntax is CONSTRUCTIONNAME | first rule A second rule A third rule for example:"
val comment3 = "parseinput ''ThreeRulesTogether | [Vs1| Vs2 (s |s1|, |s2| = l |s2|, |s1| * s |s1| |s2| = |s2| |s1|)] A [second rule] A [third rule]nger s2, s1)] A [second rule] A [third rule]''] 0" 
val comment4 = "the order of splitting within rules is: quants > equivalence/implies > = > and > not >  predicates"

(*TCPair ({token = token, constructor = constructor}, cs)*)

signature PARSERMEAS =
sig 
    val splitRules: char list -> char -> string list
    val parseRule: int -> construction -> string -> int -> construction
    val joinAnds: construction list -> construction
    val reverse: 'a list -> 'a list
    val extract_name: char list -> string
    val inputIntoConstructionData: string -> constructionData
    val exists: char list -> bool
    val afterDiv: char list -> string
    val beforeSep: char list -> char -> string
    val afterSep: char list -> char -> char list -> string
end;

structure parserMeas : PARSERMEAS =
struct
  exception ParseError of string;
  exception CodeError;

fun splitRules L sep =
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
    end;

  (*val parseRule_sig = "takes in string to parse and accumulator construction (whatever was already parsed) and recursively moves things from string to acc in order from above";

  val joinAnds_sig = "takes in list of rules to turn into contruction of ands";*)

  fun exist (_, []) = false
    | exist (x, y::ys) = (x = y) orelse exist (x, ys)

  fun joinAnds d xs = 
    case (xs) of
        | (x :: y) => 
        let val rest = joinAnds (no+1) y in
        TCPair({constructor = (logicInfixOp, ([formula, binary, ...], formula)), token =("rule" ^ (Int.toString d), "formula")},
        [x, Source ("and", "binary"),rest])
        | (x :: []) => x
    end;

(**)

  fun beforeSep ch [] acc = (String.explode acc)
      | beforeSep ch (x::xs) acc = if x = ch then acc else beforeSep ch [] (String.explode (acc @ x))

  fun afterSep ch [] = []
      | afterSep ch (x::xs) = if x = ch then xs else x::afterSep ch (xs)

  fun parseRule d stri =
  let val str = String.implode stri in
  if exists(str, #"V") then TCPair({constructor = ("logicApplyQuant", ([formula, binary, ...], formula)), token =("tqnt"^Int.toString d, "formula")},
                      [Source ("q"^Int.toString d, "forall"), Source ("s"^Int.toString d, (extract_name str) ^":seg"), parseRule (d+1) (afterDiv str)])  orelse
  if exists (str, #">") then 
                      let val left = beforeSep #">" str
                      let val right = afterSep #">" str [] in
                      TCPair({constructor = ("logicInfixOp", ([formula, binary, ...], formula)), token =("timp"^Int.toString d, "formula")},
                      [parseRule (d+1) left, Source ("implies", "binary"), (d+1) parseRule right])  orelse
  if exists (str, #"*") then 
                      let val left = beforeSep #"*" str
                      let val right = afterSep #"*" str [] in
                      TCPair({constructor = ("logicInfixOp", ([formula, binary, ...], formula)), token =("teqv"^Int.toString d, "formula")},
                      [parseRule (d+1) left, Source ("equiv", "binary"), (d+1) parseRule right])  orelse
  if exists (str, #"&") then 
                      let val left = beforeSep #"&" str
                      let val right = afterSep #"&" str [] in
                      TCPair({constructor = ("logicInfixOp", ([formula, binary, ...], formula)), token =("tand"^Int.toString d, "formula")},
                      [parseRule (d+1) left, Source ("and", "binary"), (d+1) parseRule right])  orelse
  (*if exists (str, #"=") then orelse
  if exists (str, #"~") then orelse
  if exists (str, #"S") then orelse
  if exists (str, #"L") then orelse*)  
  (*the only left thing is a segment, which might have a name/token-type*)
  
  if String.isPrefix "|" stri then
  Source (s^Int.toString d, (extract_name String.extract (stri, 1, NONE))^":"^"segment") else  Source(s^Int.toString d, "segment")
  end;

  fun reverse nil = nil | reverse (x::xs) = (reverse xs) @ [x]

  fun extract_name (x::xs) acc =
   if x = #"|" then String.implode (reverse acc) else extract_name xs (x :: acc)

  fun afterdiv Nil = 0
  | afterdiv (x::xs) if x == #"|" then xs else afterdiv xs

  fun stringToConstruct (y::ys) 0 = String.implode ys
    |stringToConstruct (y::ys) l = stringToConstruct ys (l-1);

  fun inputIntoConstructionData stri =
    let val str = String.stripSpaces stri
    let val name = extract_name (String.explode str) [] 
    let val consSpecN = "measStickG" in
    let val toConstruct = stringToConstruct(String.explode str) (String.size name) in
    let val construction = joinAnds(List.map (parseRule 1) (splitRules (String.explode toConstruct))) in
    constructionData = {name = name, conSpecN = conSpecN, construction = construction}
    end;
