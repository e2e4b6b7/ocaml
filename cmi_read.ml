open Stdlib

type alerts = string Stdlib.String.Map.t

type pers_flags =
  | Rectypes
  | Alerts of alerts
  | Opaque
  | Unsafe_string

type error =
  | Not_an_interface of filepath
  | Wrong_version_interface of filepath * string
  | Corrupted_interface of filepath

exception Error of error

(* these type abbreviations are not exported;
   they are used to provide consistency across
   input_value and output_value usage. *)
type signature = Types.signature_item list
type flags = pers_flags list
type header = modname * signature

type cmi_infos = {
    cmi_name : string;
    cmi_sign : signature;
    cmi_crcs : crcs;
    cmi_flags : flags;
}

let input_cmi ic =
  let (name, sign) = (input_value ic : header) in
  let crcs = (input_value ic : crcs) in
  let flags = (input_value ic : flags) in
  {
      cmi_name = name;
      cmi_sign = sign;
      cmi_crcs = crcs;
      cmi_flags = flags;
    }

let read_cmi filename l =
  let ic = open_in_bin filename in
  try
    let _magic_number = really_input_string ic l in
    let cmi = input_cmi ic in
    close_in ic;
    cmi
  with
    | End_of_file | Failure _ ->
      close_in ic;
      Printf.printf ""
      raise End_of_file
    | Error e ->
      close_in ic;
      raise (Error e)