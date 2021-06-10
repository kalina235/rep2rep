import "composition";

signature LATEX =
sig
  val construction : real * real -> Construction.construction -> string;
  val mkDocument : string -> string;
  val outputDocument : TextIO.outstream -> string -> unit;
end;

structure Latex : LATEX =
struct

  fun realToString z =
    let val zs = Real.toString z
    in case String.explode zs of (#"~"::n) => ("-" ^ String.implode n) | _ => zs
    end

  fun intToString z =
    let val zs = Int.toString z
    in case String.explode zs of (#"~"::n) => ("-" ^ String.implode n) | _ => zs
    end

  fun lines [h] = h
    | lines (h::t) = h ^ "\n " ^ lines t
    | lines _ = raise Empty

  fun nodeNameOfToken t = String.addParentheses (CSpace.nameOfToken t ^ "" ^ TypeSystem.nameOfType (CSpace.typeOfToken t))
  fun nodeNameOfConfigurator u t =
    let val nu = CSpace.nameOfConfigurator u
        val c = CSpace.constructorOfConfigurator u
        val nc = CSpace.nameOfConstructor c
        val tn = (CSpace.nameOfToken t ^ "" ^ TypeSystem.nameOfType (CSpace.typeOfToken t))
    in String.addParentheses (nu ^ "_" ^ nc ^ "_" ^ tn)
    end

  fun coordinates (x,y) = String.addParentheses (realToString x ^ "," ^ realToString y)

  fun configuratorNode coor u t =
    let val nu = CSpace.nameOfConfigurator u
        val c = CSpace.constructorOfConfigurator u
        val nc = "$\\mathit{"^CSpace.nameOfConstructor c^"}$"
        val nodeString = ""
    in "\\node[constructor = " ^ String.addBraces nc ^ "] " ^ nodeNameOfConfigurator u t ^ " at " ^ coordinates coor ^ " " ^ String.addBraces nodeString ^ ";"
    end

  fun tokenNode isSource coor t =
    let val typn = "$\\mathsf{"^TypeSystem.nameOfType (CSpace.typeOfToken t)^"}$"
        val tokn = "$"^CSpace.nameOfToken t^"$"
        val att = if isSource then "termS" else "term"
    in "\\node["^att^" = " ^ String.addBraces typn ^ "] " ^ nodeNameOfToken t ^ " at " ^ coordinates coor ^ " " ^ String.addBraces tokn ^ ";"
    end

  fun arrowBent nodeName parentName (ix,ox) =
    "\\path[->,in=" ^intToString ix^",out="^intToString ox ^"] " ^ nodeName ^ " edge " ^ parentName ^ ";"

  fun arrow nodeName parentName =
    "\\path[->] " ^ nodeName ^ " edge " ^ parentName ^ ";"

  fun arrowLabelled nodeName parentName i =
    "\\path[->] " ^ nodeName ^ " edge node[index label] " ^ String.addBraces (intToString i) ^ " " ^ parentName ^ ";"
  fun arrowLabelledBent nodeName parentName i (ix,ox)=
    "\\path[->,in=" ^intToString ix^",out="^intToString ox ^ "] " ^ nodeName ^ " edge node[index label] " ^ String.addBraces (intToString i) ^ " " ^ parentName ^ ";"

  fun quickWidthEstimate (Construction.Source t) =
        let val sizeOfToken = real (String.size (CSpace.nameOfToken t))
            val sizeOfType = 0.75 * real (String.size (TypeSystem.nameOfType (CSpace.typeOfToken t)))
        (*in Real.max(0.75,0.1*real (Int.max(sizeOfToken,sizeOfType)))*)
        in Real.max(0.75,0.12* (Real.max(sizeOfToken, sizeOfType)))
        end
    | quickWidthEstimate (Construction.Loop _) = 0.0
    | quickWidthEstimate (Construction.TCPair (_,cs)) = List.sumMap quickWidthEstimate cs

  fun construction' coor parentName i (Construction.Source t) =
        (case parentName of
          NONE => lines [tokenNode true coor t]
        | SOME pn => lines [tokenNode true coor t, arrowLabelled (nodeNameOfToken t) pn i])
    | construction' _ parentName i (Construction.Loop t) =
        (case parentName of
          NONE => "% BAD CONSTRUCTION"
        | SOME pn => if i = 1 then lines [arrowLabelledBent (nodeNameOfToken t) pn i (180,195)] else lines [arrowLabelledBent (nodeNameOfToken t) pn i (0,~15)])
    | construction' (x,y) parentName i (Construction.TCPair ({configurator,token},cs)) =
        let val tn = tokenNode false (x,y) token
            val cn = configuratorNode (x,y-1.0) configurator token
            val configuratorNodeName = nodeNameOfConfigurator configurator token
            val cn2tn = arrow configuratorNodeName (nodeNameOfToken token)
            val widthEstimates = map (fn x => (Math.pow(quickWidthEstimate x,0.75))) cs
            fun mkIntervals _ [] = []
              | mkIntervals _ [h] = []
              | mkIntervals p (h1::(h2::t)) = (case p + (h1 + h2) of p' => p' :: mkIntervals p' (h2::t))
            val intervals = 0.0 :: mkIntervals 0.0 widthEstimates
            val cssize = List.last intervals
            fun calcX j = ~cssize/2.0 + List.nth(intervals,j)
            fun crec _ [] = []
              | crec j (ct::cts) = construction' (x + (calcX j), y-2.0) (SOME configuratorNodeName) (j+1) ct :: crec (j+1) cts
        in (case parentName of
              NONE => lines ([tn,cn,cn2tn] @ (crec 0 cs))
            | SOME pn =>
                let val tn2parent = arrowLabelled (nodeNameOfToken token) pn i
                in lines ([tn,tn2parent,cn,cn2tn] @ (crec 0 cs))
                end)
        end

  fun construction coor ct =
    let val opening = "\\begin{tikzpicture}[construction,align at top]"
        val closing = "\\end{tikzpicture}"
    in lines [opening, construction' coor NONE 0 ct, closing]
    end

  fun mkDocument content =
    let val opening = "\\documentclass[a4paper,10pt]{article}\n "^
                      "\\usepackage[margin=2.5cm]{geometry}\n "^
                      "\\input{commands.sty}\n"^
                      "\\tikzset{align at top/.style={baseline=(current bounding box.north)}}\n\n"^
                      "\\begin{document}"
        val closing = "\\end{document}"
    in lines [opening, content, closing]
    end

  fun outputDocument file content =
    let val _ = TextIO.output(file, mkDocument content)
    in () end

end;
