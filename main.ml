open Clflags
open Format
open Compenv

let interface _ppf _sourcefile _outputprefix =
  failwith "interfaces are not supported"

(* Compile a .ml file *)

let print_if ppf flag printer arg =
  if !flag then fprintf ppf "%a@." printer arg;
  arg

let (++) x f = f x

(*let (_:int) = Compile_common.implementation*)
(*
let wrap_exn exn =
  match Location.error_of_exn exn with
  | Some (`Ok e) -> Format.printf "%a\n%!" Location.report_error e
  | _ -> raise exn*)



let implementation ppf source_file output_prefix =
  Compile_common.with_info ~native:false ~tool_name:"vcaml" ~source_file ~output_prefix ~dump_ext:"dump" @@ fun info ->
  Compile_common.implementation info (fun info (t,_) -> Vcore.Driver.work info.Compile_common.source_file t)
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
  Location.input_name := name;
  if Ccomp.compile_file name <> 0 then exit 2


let process_interface_file ppf name =
  interface ppf name (output_prefix name)

let process_implementation_file ppf name =
  let opref = output_prefix name in
  implementation ppf name opref;
  objfiles := (opref ^ ".cmo") :: !objfiles

let process_file ppf name =
  Caml.Printf.printf "process_file `%s`\n%!" name;
  if Filename.check_suffix name ".ml"
  || Filename.check_suffix name ".mlt" then begin
    let opref = output_prefix name in
    implementation ppf name opref;
    objfiles := (opref ^ ".cmo") :: !objfiles
  end
  else
    raise(Arg.Bad("don't know what to do with " ^ name))

let usage = "Usage: ocamlc <options> <files>\nOptions are:"

let ppf = Format.err_formatter

let before_compile s =
  (* in 4.02 we ignore argument *)
  Before_compile s

(* Error messages to standard error formatter *)
let anonymous filename =
  readenv ppf (before_compile filename); process_file ppf filename;;
let impl filename =
  try
    readenv ppf (before_compile filename);
    process_implementation_file ppf filename
  with exc ->
    Location.report_exception ppf exc;
    exit 2

let intf filename =
  readenv ppf (before_compile filename); process_interface_file ppf filename;;

let show_config () =
  Config.print_config stdout;
  exit 0;
;;


module Options = Main_args.Make_bytecomp_options (struct
  let set r () = r := true
  let unset r () = r := false
  let _a = set make_archive
  let _absname = set Clflags.absname
  let _alert = Warnings.parse_alert_option
  let _annot = set annotations
  let _binannot = set binary_annotations
  let _c = set compile_only
  let _cc s = c_compiler := Some s
  let _cclib s = Compenv.defer (ProcessObjects (Misc.rev_split_words s))
  let _ccopt s = first_ccopts := s :: !first_ccopts
  let _compat_32 = set bytecode_compatible_32
  let _config = Misc.show_config_and_exit
  let _config_var = Misc.show_config_variable_and_exit
  let _custom = set custom_runtime
  let _no_check_prims = set no_check_prims
  let _dllib s = defer (ProcessDLLs (Misc.rev_split_words s))
  let _dllpath s = dllpaths := !dllpaths @ [s]
  let _for_pack s = for_package := Some s
  let _g = set debug
  let _i () =
    print_types := true;
    compile_only := true;
    stop_after := Some Compiler_pass.Typing;
    ()
  let _stop_after pass =
    let module P = Compiler_pass in
    begin match P.of_string pass with
    | None -> () (* this should not occur as we use Arg.Symbol *)
    | Some pass ->
        stop_after := Some pass;
        begin match pass with
        | P.Parsing | P.Typing ->
            compile_only := true
        end;
    end
  let _I s = include_dirs := s :: !include_dirs
  let _impl = impl
  let _intf = intf
  let _intf_suffix s = Config.interface_suffix := s
  let _keep_docs = set keep_docs
  let _no_keep_docs = unset keep_docs
  let _keep_locs = set keep_locs
  let _no_keep_locs = unset keep_locs
  let _labels = unset classic
  let _linkall = set link_everything
  let _make_runtime () =
    custom_runtime := true; make_runtime := true; link_everything := true
  let _alias_deps = unset transparent_modules
  let _no_alias_deps = set transparent_modules
  let _app_funct = set applicative_functors
  let _no_app_funct = unset applicative_functors
  let _noassert = set noassert
  let _nolabels = set classic
  let _noautolink = set no_auto_link
  let _nostdlib = set no_std_include
  let _o s = output_name := Some s
  let _opaque = set opaque
  let _open s = open_modules := s :: !open_modules
  let _output_obj () = output_c_object := true; custom_runtime := true
  let _output_complete_obj () =
    output_c_object := true;
    output_complete_object := true;
    custom_runtime := true
  let _pack = set make_package
  let _pp s = preprocessor := Some s
  let _ppx s = first_ppx := s :: !first_ppx
  let _plugin _p = plugin := true
  let _principal = set principal
  let _no_principal = unset principal
  let _rectypes = set recursive_types
  let _no_rectypes = unset recursive_types
  let _runtime_variant s = runtime_variant := s
  let _with_runtime = set with_runtime
  let _without_runtime = unset with_runtime
  let _safe_string = unset unsafe_string
  let _short_paths = unset real_paths
  let _strict_sequence = set strict_sequence
  let _no_strict_sequence = unset strict_sequence
  let _strict_formats = set strict_formats
  let _no_strict_formats = unset strict_formats
  let _thread = set use_threads
  let _vmthread = fun () -> fatal "vmthread_removed_message"
  let _unboxed_types = set unboxed_types
  let _no_unboxed_types = unset unboxed_types
  let _unsafe = set unsafe
  let _unsafe_string = set unsafe_string
  let _use_prims s = use_prims := s
  let _use_runtime s = use_runtime := s
  let _v () = print_version_and_library "compiler"
  let _version = print_version_string
  let _vnum = print_version_string
  let _w = (Warnings.parse_options false)
  let _warn_error = (Warnings.parse_options true)
  let _warn_help = Warnings.help_warnings
  let _color = Misc.set_or_ignore color_reader.parse color
  let _error_style = Misc.set_or_ignore error_style_reader.parse error_style
  let _where = print_standard_library
  let _verbose = set verbose
  let _nopervasives = set nopervasives
  let _match_context_rows n = match_context_rows := n
  let _dump_into_file = set dump_into_file
  let _dno_unique_ids = unset unique_ids
  let _dunique_ids = set unique_ids
  let _dsource = set dump_source
  let _dparsetree = set dump_parsetree
  let _dtypedtree = set dump_typedtree
  let _drawlambda = set dump_rawlambda
  let _dlambda = set dump_lambda
  let _dinstr = set dump_instr
  let _dcamlprimc = set keep_camlprimc_file
  let _dtimings () = profile_columns := [ `Time ]
  let _dprofile () = profile_columns := Profile.all_columns

  let _args = Arg.read_arg
  let _args0 = Arg.read_arg0

  let anonymous = anonymous
end)

let all_options =
  ("-newstyle", Arg.Unit (fun () -> () ),
               "just a stub for possible option")
  :: Options.list

let () =
  let set_size fmt =
    let sz = Option.value ~default:170 (Terminal_size.get_columns ()) in
    Format.printf "terminal width = %d\n%!" sz;
    Format.pp_set_margin fmt (sz-1);
    Format.pp_set_max_indent fmt 2000 (* (sz-1) *)
  in
  set_size Format.std_formatter;
  set_size Format.err_formatter;
  readenv ppf Before_args;
  Arg.parse all_options anonymous usage;
  ()
