open Yojson.Basic.Util

module StringSet = Set.Make(String)
module StringMap = Map.Make(String)

type fun_info =
  { name : string;
    arg_typs : string list;
    ret_typ : string;
    effects : StringSet.t;
    calls : StringSet.t;
    regs_read : StringSet.t;
    regs_written : StringSet.t;
    trans_regs_read : StringSet.t;
    trans_regs_written : StringSet.t
  }

let fun_info_of_json j =
  { name = member "name" j |> to_string;
    arg_typs = member "arg_typs" j |> convert_each to_string;
    ret_typ = member "ret_typ" j |> to_string;
    effects = member "effects" j |> convert_each to_string |> StringSet.of_list;
    calls = member "calls" j |> convert_each to_string |> StringSet.of_list;
    regs_read = member "regs_read" j |> convert_each to_string |> StringSet.of_list;
    regs_written = member "regs_written" j |> convert_each to_string |> StringSet.of_list;
    trans_regs_read = member "trans_regs_read" j |> convert_each to_string |> StringSet.of_list;
    trans_regs_written = member "trans_regs_written" j |> convert_each to_string |> StringSet.of_list;
  }

let effectful f = not (StringSet.is_empty f.effects)

let load_fun_infos skip file =
  Yojson.Basic.from_file file
  |> member "fun_infos"
  |> to_list
  |> List.map fun_info_of_json
  |> List.filter (fun f -> effectful f && not (StringSet.mem f.name skip));

type isa =
  { name : string;
    cap_regs : StringSet.t;
    privileged_regs : StringSet.t;
    cap_inv_regs : StringSet.t;
    mem_inv_regs : StringSet.t;
    conf_regs : StringSet.t;
    cap_types : StringSet.t;
    fun_infos : fun_info list;
    fun_renames : string StringMap.t;
    reg_ref_renames : string StringMap.t;
  }

let load_isa file =
  { name = "CHERI_RISCV";
    cap_regs = StringSet.of_list ["MEPCC";
                                  "MScratchC";
                                  "MTDC";
                                  "MTCC";
                                  "SEPCC";
                                  "SScratchC";
                                  "STDC";
                                  "STCC";
                                  "UEPCC";
                                  "UScratchC";
                                  "UTDC";
                                  "UTCC";
                                  "DDC";
                                  "nextPCC";
                                  "PCC";
                                  "x31";
                                  "x30";
                                  "x29";
                                  "x28";
                                  "x27";
                                  "x26";
                                  "x25";
                                  "x24";
                                  "x23";
                                  "x22";
                                  "x21";
                                  "x20";
                                  "x19";
                                  "x18";
                                  "x17";
                                  "x16";
                                  "x15";
                                  "x14";
                                  "x13";
                                  "x12";
                                  "x11";
                                  "x10";
                                  "x9";
                                  "x8";
                                  "x7";
                                  "x6";
                                  "x5";
                                  "x4";
                                  "x3";
                                  "x2";
                                  "x1";
                                  "Xs";];
    privileged_regs = StringSet.of_list [
      "UTCC"; "UTDC"; "UScratchC"; "UEPCC"; "STCC"; "STDC"; "SScratchC"; "SEPCC"; "MTCC"; "MTDC"; "MScratchC"; "MEPCC"; "uccsr"; "sccsr"; "mccsr"];
    cap_inv_regs = StringSet.of_list ["PCC"];
    mem_inv_regs = StringSet.of_list [];
    conf_regs = StringSet.of_list [];
    cap_types = StringSet.of_list ["Capability"];
    fun_infos = load_fun_infos (StringSet.of_list []) file;
    fun_renames = StringMap.empty;
    reg_ref_renames = StringMap.empty;
  }
