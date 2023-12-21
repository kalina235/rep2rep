import "util.sequence";
signature LOGICMANAGE =
sig 
   (* val extractPrincipalTypes : string -> string -> unit*)
    val fix : Construction.construction -> string
    val hash : Construction.construction -> int
     (*val filterWarnings : string -> Rpc.endpoint (*given document name, throw out tSchemas with warnings *)*)
end;

structure logicManage : LOGICMANAGE =
  struct
    exception StringParseError of string;
    exception CodeError;
    fun nth n []  = raise CodeError
    | nth n (x::xs) = if n > 0 then (nth (n-1) xs) else x;

  (*fun extractPrincipalTypes doc name=
        let val dc = Document.read doc
            val allTs = List.map #typ (#principalTypes (Document.findTypeSystemDataWithName  dc name))
            val logicTs = List.map #typ (#principalTypes (Document.findTypeSystemDataWithName  dc "firstOrderLogic"))
            val baseTs = List.filter (fn x => List.all (fn y => x <> y) logicTs) allTs  (*(this is subtracting firstOrderLogicTS from inquired type system)*)
            val outString = String.concat (List.map (fn x => x^" ") baseTs);
            val outputFile = TextIO.openOut ("src/semanticRelations/"^name^"Types")
            in TextIO.output(outputFile, outString);TextIO.closeOut outputFile end;*)

 (*) *)
  (*  fun fastPow n x mod=
      if n == 0 then 0 else
      if x == 0 then 1 else
      if x % 2 == 1 then (fastpow (n*n) (x-1) % mod)  else  (fastpow (fastpow n (x/2) % mod)*(fastpow n (x/2) % mod))
    fun addChil i [] = 0
      | addChil i (x::xy) = (i*x) + addChil (i+1) xy
    
    fun charListToNum [] = 0
      | charListToNum (x::xy) = Char.ord x + charListToNum xy

(**)

  (*val sigconstructtionToFormula= flatten a tree into an expression*)*)

    fun power (x, 0) = 1  
    | power (x, n) = x * power(x, n-1) mod 10000019; 

    fun typeToNum num typ =
      let val str = String.explode typ in
      case str of
        [] => num mod 27
        | x::xs => typeToNum (num + Char.ord x) (String.implode xs) end

    fun mapMap f [] = []
      | mapMap f (x::xs) = (f x) :: (List.map f xs)

    fun sum [] = 0
      | sum (x::xs) = x + sum xs

    fun childHash func clist =
        case clist of 
          [] => []
        | x :: xs =>  (power (func x, (List.length clist))) :: (List.map func clist);

    fun hash conn =
        case conn of
              Construction.Source(tok, ty) =>  typeToNum 0 ty
            | Construction.TCPair({token, constructor =(a,  (xs, ct))}, clist) => (sum (childHash hash clist)) mod 10000019
            | _ => raise StringParseError("You probably have a loop")

    fun constructionToFormula con = 
        case con of
             Construction.Source(tok, ty) => if String.substring(tok, 0, 1) = "s" then "v"^(String.substring (ty, 0, 2)) else ty (*is subtype of object*)
            | Construction.TCPair({token, constructor =(a,  (xs, ct))}, clist) => ((String.concat (List.map constructionToFormula clist)))
            | _ => raise StringParseError("You probably have a loop")

    fun fix con = 
    let fun fixup cl = 
      case cl of
        [] => []
      | #"f":: #"o":: #"r"::xs => (#" ":: #"V":: #" "::(fixup ((List.tl o List.tl o List.tl) xs)))
      | #"o":: #"r"::xs => (#" " :: #"v" :: #" "::(fixup xs))
      | #"a":: #"n":: #"d"::xs => (#" ":: #"&":: #" "::(fixup xs))
      | #"e":: #"q":: #"u":: #"a"::xs => (#" ":: #"=":: #" "::(fixup (List.tl xs)))
      | #"e":: #"q":: #"u"::xs => (#" ":: #"<":: #"=":: #">":: #" "::(fixup ((List.tl o List.tl) xs)))
      | #"i":: #"m":: #"p"::xs => (#" ":: #"=":: #">":: #" "::(fixup ((List.tl o List.tl o List.tl o List.tl) xs)))
      | #"n":: #"o":: #"t"::xs => (#" ":: #"~"::(fixup xs))
      | #"v"::xs => (#" "::fixup xs)
      | _ => ((List.hd cl) :: (fixup (List.tl cl)))
    in String.implode (fixup (String.explode (constructionToFormula con)))
    end;

end;

