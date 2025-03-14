import "util.logging";
import "latex.latex";
import "oruga.document";
import "server.server";

(* To see a full trace of the algorithm, we enable logging.
   If this seems too 'noisy', you can use `Logging.disable ()`.
   (Alternatively, because disabled is the default logging state,
   you can just comment out the following line.)
*)
Logging.enable ();

fun runServer addr transferMap files =
    let val rpc_service = Rpc.create addr;
        val endpoints = Server.make files transferMap;
        val _ = print "Starting RPC server...\n";
    in Rpc.serve rpc_service endpoints end;

fun filesMatchingPrefix dir prefix =
    let
        fun getWholeDir direc out = case OS.FileSys.readDir (direc) of
                                      SOME f => getWholeDir direc (f::out)
                                    | NONE => List.rev out;
        val dirstream = OS.FileSys.openDir dir;
        val filenames = getWholeDir dirstream [];
        val filteredFiles = List.filter (String.isPrefix prefix) filenames;
        fun attachDir p = dir ^ p;
    in
        map (OS.FileSys.realPath o attachDir) filteredFiles
    end
    handle OS.SysErr (a, b) => (raise OS.SysErr (a, b));

exception BadArguments
datatype args = ServerMode of ((string * int) * string list * (string * string * string) list)
              | DocumentMode of string
fun parseArgs () =
  let val args = CommandLine.arguments ();
      val configuration =
          (case args of
               ("--server-address"::address::"--server-port"::port::files)
               => (case Int.fromString port of
                       SOME port =>
                       (case files of
                            ("--transfer-map"::mapfile::files) =>
                            ServerMode ((address, port), files, Server.readTransferMap mapfile)
                          | _ => ServerMode((address, port), files, []))
                     | NONE => raise BadArguments)
             | [documentName] => DocumentMode documentName
             | _ => raise BadArguments)
  in configuration end;

fun main () =
  let val today = Date.fmt "%Y-%m-%d" (Date.fromTimeLocal (Time.now()));
      val version = "rep2rep-" ^ REP2REP_VERSION;
  (*)    val _ = Logging.write ("BEGIN algorithm-trace-"
                               ^ today
                               ^ " with "
                               ^ version ^ "\n");*)
  in case parseArgs () of
         DocumentMode documentName => (Document.read documentName; ())
       | ServerMode (addr, files, transferMap) => (Logging.write (List.toString (fn s => s) files);
                                      runServer addr transferMap files)
  end
