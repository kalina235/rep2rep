import "core.type";


(* An underlying assumption of having token = string * type is that two tokens in a
  cspace are different if and only if their string type pairs are different.*)
signature CSPACE =
sig
  type ctyp = Type.typ list * Type.typ
  type constructor
  (*datatype atom = Token of string | Variable of string;*)
  type token(* = string * Type.typ;*)
  type configurator
  type conSpec = {name : string, typeSystem : string, constructors : constructor FiniteSet.set}

  val ctyp_rpc : ctyp Rpc.Datatype.t;
  val constructor_rpc : constructor Rpc.Datatype.t;
  val token_rpc : token Rpc.Datatype.t;
  val configurator_rpc : configurator Rpc.Datatype.t;
  val conSpec_rpc : conSpec Rpc.Datatype.t;

  val makeCTyp : Type.typ list * Type.typ -> ctyp
  val makeConstructor : string * ctyp -> constructor
  val makeConfigurator : string * constructor -> configurator
  val makeToken : string -> Type.typ -> token

  val csig : constructor -> ctyp
  val nameOfConfigurator : configurator -> string;
  val nameOfConstructor : constructor -> string;
  val constructorOfConfigurator : configurator -> constructor;
  val typesOfConfigurator : configurator -> ctyp
  val sameConstructors : constructor -> constructor -> bool
  val sameConfigurators : configurator -> configurator -> bool
  val sameTokens : token -> token -> bool
  val tokensHaveSameType : token -> token -> bool
  val nameOfToken : token -> string
  val typeOfToken : token -> Type.typ
  val findConstructorWithName : string -> conSpec -> constructor option
  val stringOfToken : token -> string
  val stringOfConstructor : constructor -> string
  val stringOfConfigurator : configurator -> string

  val wellDefinedConSpec : Type.typeSystemData -> conSpec -> (bool * bool * bool)
  exception ImpossibleOverload
  val fixClashesInConSpec : Type.typeSystemData -> conSpec -> (Type.typeSystemData * conSpec)
end;

structure CSpace : CSPACE =
struct
  type ctyp = Type.typ list * Type.typ
  type constructor = string * ctyp
  (*datatype atom = Token of string | Variable of string;*)
  type token = string * Type.typ
  type configurator = string * constructor
  type conSpec = {name : string, typeSystem : string, constructors : constructor FiniteSet.set}

  val ctyp_rpc = Rpc.Datatype.alias
                     "CSpace.ctyp"
                     (Rpc.Datatype.tuple2
                          (List.list_rpc Type.typ_rpc,
                           Type.typ_rpc));

  val constructor_rpc = Rpc.Datatype.alias
                            "CSpace.constructor"
                            (Rpc.Datatype.tuple2 (String.string_rpc, ctyp_rpc));

  val token_rpc = Rpc.Datatype.alias
                      "CSpace.token"
                      (Rpc.Datatype.tuple2 (String.string_rpc, Type.typ_rpc));

  val configurator_rpc = Rpc.Datatype.alias
                             "CSpace.configurator"
                             (Rpc.Datatype.tuple2
                                  (String.string_rpc, constructor_rpc));

  val conSpec_rpc = Rpc.Datatype.convert
                        "CSpace.conSpec"
                        (Rpc.Datatype.tuple3
                             (String.string_rpc,
                              String.string_rpc,
                              FiniteSet.set_rpc constructor_rpc))
                        (fn (n, ts, cs) => {name = n,
                                            typeSystem = ts,
                                            constructors = cs})
                        (fn {name = n,
                             typeSystem = ts,
                             constructors = cs} => (n, ts, cs));


  fun makeCTyp x = x
  fun makeConstructor x = x
  fun makeConfigurator x = x
  fun makeToken s ty = (s,ty)

  fun csig (s,ctyp) = ctyp
  fun nameOfConfigurator (u,_) = u
  fun nameOfConstructor (cn,_) = cn
  fun constructorOfConfigurator (_,c) = c
  fun typesOfConfigurator (u,c) = csig c

  fun sameConstructors (n,(tyL,ty)) (n',(tyL',ty')) =
    (n = n' andalso Type.equal ty ty' andalso List.allZip Type.equal tyL tyL');
  fun sameConfigurators (u,c) (u',c') = (u = u' andalso sameConstructors c c');
  fun sameTokens (t,ty) (t',ty') = (t = t' andalso Type.equal ty ty');
  fun nameOfToken (t,_) = t;
  fun typeOfToken (_,ty) = ty;
  fun tokensHaveSameType (_,ty) (_,ty') = Type.equal ty ty';

  fun findConstructorWithName s cspec =
    List.find (fn c => nameOfConstructor c = s) (#constructors cspec)
  fun stringOfToken (t,ty) = t ^ ":" ^ (Type.nameOfType ty)
  fun stringOfConstructor (c,(tys,ty)) = c ^ " : " ^ (String.stringOfList Type.nameOfType tys) ^ " -> " ^ ty
  fun stringOfConfigurator (u,cc) = u ^ ":" ^ stringOfConstructor cc


  fun wellDefinedConSpec TSD {name,typeSystem,constructors} =
    let
      val Ty = #Ty (#typeSystem TSD)
      fun clashes (s,ctyp) (s',ctyp') =
        if s = s' andalso ctyp <> ctyp'
        then (print ("WARNING: type " ^ s ^ " is defined twice with different signatures\n"); true)
        else false
      fun noClashes [] = true
        | noClashes ((s,(inTyps,outTyp))::L) = not (List.exists (clashes (s,(inTyps,outTyp))) L) andalso noClashes L
      val nameMatches =
        if #name TSD = typeSystem
        then true
        else (print ("WARNING: " ^ #name TSD ^ " is not " ^ typeSystem ^ "\n"); false)
      fun goodTypes [] = true
        | goodTypes (typ::L) =
            if Set.elementOf typ Ty
            then goodTypes L
            else (print ("WARNING: type " ^ (Type.nameOfType typ) ^ " is not in " ^ typeSystem ^ "\n"); false)
      fun nonEmptyInput s inTyps =
        if inTyps = []
        then (print ("WARNING: Empty input types for " ^ s ^ "\n"); false)
        else true
      fun checkConstructors [] = []
        | checkConstructors ((s,(inTyps,outTyp))::L) =
            nonEmptyInput s inTyps ::
            goodTypes (outTyp :: inTyps) ::
            checkConstructors L
      val wellDefinedConstructors = List.all (fn x => x) (checkConstructors constructors)
    in (nameMatches, wellDefinedConstructors, noClashes constructors)
    end


  exception ImpossibleOverload
  fun extendWithManyLCSuperTypes (TP as {typeSystem,principalTypes}) (ty::tys) (ty'::tys') =
        (case Type.addLeastCommonSuperType TP ty ty' of
          (lcspt,TP') => (case extendWithManyLCSuperTypes TP' tys tys' of
                            (L,TP'') => (lcspt::L,TP'')))
    | extendWithManyLCSuperTypes X [] [] = ([],X)
    | extendWithManyLCSuperTypes _ _ _ = raise ImpossibleOverload

  fun fixClashesInConSpec TSD {name,typeSystem,constructors} =
    let
      fun clash (s,(inTyps,outTyp)) (s',(inTyps',outTyp')) =
        s = s' andalso (inTyps,outTyp) <> (inTyps',outTyp')

      fun findClashes L =
        let fun findClashes' [] = []
              | findClashes' (c::L') =
                  (case List.partition (clash c) L' of (Cl,NCl) => (c,Cl) :: findClashes' NCl)
            val (clashes,F) = List.partition (fn (_,Y) => Y <> []) (findClashes' L)
            fun getNonclashing [] = []
              | getNonclashing ((c,_)::L') =
                  if List.exists (fn (x,_) => nameOfConstructor c = nameOfConstructor x) clashes
                  then getNonclashing L'
                  else c :: getNonclashing L'
            val nonclashing = getNonclashing F
        in (clashes, nonclashing)
        end

      fun resolveClash TP ((s,(inTyps,outTyp)), (s',(inTyps',outTyp'))) =
        let val (otyp::ityps,updatedTP) = extendWithManyLCSuperTypes TP (outTyp::inTyps) (outTyp'::inTyps')
        in ((s,(ityps,otyp)),updatedTP)
        end

      fun resolveClashesForConstructor TP (c,[]) = (c,TP)
        | resolveClashesForConstructor TP (c,(c'::L')) =
            case resolveClash TP (c,c') of
              (d,nextTP) => resolveClashesForConstructor nextTP (d,L')

      fun resolveClashes TP [] = ([],TP)
        | resolveClashes TP (cP::L) =
            let val (c,stepTP) = resolveClashesForConstructor TP cP
                val (cL,updatedTP) = resolveClashes stepTP L
            in (c::cL,updatedTP)
            end

      val TP = {typeSystem = #typeSystem TSD, principalTypes = #principalTypes TSD}

      val (clashes,nonclashing) = findClashes (FiniteSet.listOf constructors)
      val (newConstructors,updatedTP) = resolveClashes TP clashes
      val updatedConstructors = FiniteSet.ofList (newConstructors @ nonclashing)

      val updatedTSD = {typeSystem = #typeSystem updatedTP,
                        principalTypes = #principalTypes updatedTP,
                        name = #name TSD}
      val _ = print ("  SUCCESSFULLY REPLACED ALL CLASHES WITH CONSTRUCTORS WITH GENERALISED SIGNATURES (EXPERIMENTAL):\n")
      val _ = map ((fn x => Logging.write ("  " ^ x ^ "\n")) o stringOfConstructor) newConstructors

      val _ = findClashes
    in (updatedTSD, {name = name, typeSystem = typeSystem, constructors = updatedConstructors})
    end handle ImpossibleOverload => (Logging.write "ERROR: Impossible to fix clash in constructor specification :-( \n"; raise ImpossibleOverload)
end;
