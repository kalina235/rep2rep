fun filterTschemas ics docname =
let val dc = Document.read docname
    val tschemas = #tschemas dc
    in InterCSpace.toString (List.flatten ((List.apply (fun t -> if InterCSpace.wellFormedTransferSchema ics t then [] else [t]), tschemas))