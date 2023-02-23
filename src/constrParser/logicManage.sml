signature LOGICMANAGE =
sig 
    val constructionToFormula : Construction.construction -> string -> string
    val extractPrincipalTypes : string -> string -> Rpc.endpoint
   (*) val filterWarnings : string -> Rpc.endpoint (*given document name, throw out tSchemas with warnings*)*)
end;


structure logicManage : LOGICMANAGE =
  struct
    exception StringParseError of string;
    exception CodeError;

    fun extractPrincipalTypes doc name=
        let val dc = Document.read doc
            val allTs = List.map #typ (#principalTypes (Document.findTypeSystemDataWithName  dc name))
            val logicTs = List.map #typ (#principalTypes (Document.findTypeSystemDataWithName  dc "firstOrderLogic"))
            val baseTs = List.filter (fn x => List.all (fn y => x <> y) logicTs) allTs  (*(this is subtracting firstOrderLogicTS from inquired type system)*)
            val outString = String.concat (List.map (fn x => x^" ") baseTs);
            val outputFile = TextIO.openOut ("src/semanticRelations/"^name^"Types")
            in TextIO.output(outputFile, outString);TextIO.closeOut outputFile end;
        
    fun constructionToFormula con doc = 
        let val dc = Document.read doc
            in
        case con of
             Construction.Source(tok, ty) => (String.extract (tok, 0, 2))
            | Construction.TCPair({token, constructor =(a,x:y:z:t)}, clist), ty) => 
                                               if a = "logicInfixOp" or a = "infixBinRel" then constructionToFormula clist.hd ^ y ^ constructionToFormula List.hd.hd.hd clist else
                                                x^(String.concat (constructionToFormula clist))
        end;

end;

