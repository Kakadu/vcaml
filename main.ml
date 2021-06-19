open Clflags
open Format
open Compenv

let interface _ppf _sourcefile _outputprefix =
  failwith "interfaces are not supported"

(* Compile a .ml file *)

let print_if ppf flag printer arg =
  if !flag then fprintf ppf "%a@." printer arg ;
  arg

let ( ++ ) x f = f x

(*let (_:int) = Compile_common.implementation*)
(*
let wrap_exn exn =
  match Location.error_of_exn exn with
  | Some (`Ok e) -> Format.printf "%a\n%!" Location.report_error e
  | _ -> raise exn*)

let implementation ppf source_file output_prefix =
  Compile_common.with_info ~native:false ~tool_name:"vcaml" ~source_file
    ~output_prefix ~dump_ext:"dump"
  @@ fun info ->
  Compile_common.implementation info (fun info (t, _) ->
      Vcore.Driver.work info.Compile_common.source_file t )
(*
  Compmisc.init_path ();
  let modulename = module_of_filename sourcefile outputprefix in
  Env.set_unit_name modulename;
  let env = Compmisc.initial_env () in
  (* let where_to_print = match !output_name with Some s -> s | None -> failwith "output file not specified" in *)
  try
    let (typedtree, _coercion) =
      Pparse.parse_implementation ~tool_name:"vcaml" sourcefile
      ++ print_if ppf Clflags.dump_parsetree Printast.implementation
      ++ print_if ppf Clflags.dump_source Pprintast.structure
      ++ Typemod.type_implementation sourcefile outputprefix modulename env
      ++ print_if ppf Clflags.dump_typedtree
        Printtyped.implementation_with_coercion
    in
    Vcore.Driver.work sourcefile typedtree
  with
    | Typetexp.Error (_loc,env,e) as exc ->
      wrap_exn exc;
(*      Typetexp.report_error env Format.std_formatter e;*)
      Format.printf "\n%!";
      raise exc
    | Typecore.Error (loc, env, err) as exc ->
        wrap_exn exc;
(*        Location.print_error Format.std_formatter loc;*)
(*        Typecore.report_error env Format.std_formatter err;*)
        exit 1
    | x -> raise x
*)

let c_file name =
  Location.input_name := name ;
  if Ccomp.compile_file name <> 0 then exit 2

let process_interface_file ppf name = interface ppf name (output_prefix name)

let process_implementation_file ppf name =
  let opref = output_prefix name in
  implementation ppf name opref ;
  objfiles := (opref ^ ".cmo") :: !objfiles

let process_file ppf name =
  Caml.Printf.printf "process_file `%s`\n%!" name ;
  if Filename.check_suffix name ".ml" || Filename.check_suffix name ".mlt" then (
    let opref = output_prefix name in
    implementation ppf name opref ;
    objfiles := (opref ^ ".cmo") :: !objfiles )
  else raise (Arg.Bad ("don't know what to do with " ^ name))

let usage = "Usage: ocamlc <options> <files>\nOptions are:"
let ppf = Format.err_formatter

let before_compile s =
  (* in 4.02 we ignore argument *)
  Before_compile s

(* Error messages to standard error formatter *)
let anonymous filename =
  readenv ppf (before_compile filename) ;
  process_file ppf filename

let impl filename =
  try
    readenv ppf (before_compile filename) ;
    process_implementation_file ppf filename
  with exc ->
    Location.report_exception ppf exc ;
    exit 2

let intf filename =
  readenv ppf (before_compile filename) ;
  process_interface_file ppf filename

let show_config () = Config.print_config stdout ; exit 0

module Options = Main_args.Make_optcomp_options (Main_args.Default.Optmain)

let all_options =
  ("-newstyle", Arg.Unit (fun () -> ()), "just a stub for possible option")
  :: Options.list

let () =
  let set_size fmt =
    let sz = Option.value ~default:170 (Terminal_size.get_columns ()) in
    Format.printf "terminal width = %d\n%!" sz ;
    Format.pp_set_margin fmt (sz - 1) ;
    Format.pp_set_max_indent fmt 2000
    (* (sz-1) *) in
  set_size Format.std_formatter ;
  set_size Format.err_formatter ;
  readenv ppf Before_args ;
  Arg.parse all_options anonymous usage ;
  ()
