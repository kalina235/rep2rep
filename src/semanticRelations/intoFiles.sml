import "oruga.document"

fun extractPrincipalTypes doc name=
let val dc = Document.read doc
    val allTs = List.map #typ (#principalTypes (Document.findTypeSystemDataWithName  dc name))
    val logicTs = List.map #typ (#principalTypes (Document.findTypeSystemDataWithName  dc "firstOrderLogic"))
    val baseTs = List.filter (fn x => List.all (fn y => x <> y) logicTs) allTs  (*(this is subtracting firstOrderLogicTS from inquired type system)*)
    val outString = String.concat (List.map (fn x => x^" ") baseTs);
    val outputFile = TextIO.openOut ("src/semanticRelations/"^name^"Base")
    in TextIO.output(outputFile, outString);TextIO.closeOut outputFile end;