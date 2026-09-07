(* Minimal JSON writer (no external dependency). *)

type t =
  | Null
  | Bool of bool
  | Int of int
  | Float of float
  | Str of string
  | List of t list
  | Obj of (string * t) list

let escape (s : string) : string =
  let b = Buffer.create (String.length s + 2) in
  String.iter
    (fun c ->
      match c with
      | '"' -> Buffer.add_string b "\\\""
      | '\\' -> Buffer.add_string b "\\\\"
      | '\n' -> Buffer.add_string b "\\n"
      | '\r' -> Buffer.add_string b "\\r"
      | '\t' -> Buffer.add_string b "\\t"
      | c when Char.code c < 0x20 -> Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c))
      | c -> Buffer.add_char b c)
    s;
  Buffer.contents b

let rec write (b : Buffer.t) (j : t) : unit =
  match j with
  | Null -> Buffer.add_string b "null"
  | Bool x -> Buffer.add_string b (if x then "true" else "false")
  | Int i -> Buffer.add_string b (string_of_int i)
  | Float f ->
    if Float.is_integer f && Float.abs f < 1e15 then
      Buffer.add_string b (Printf.sprintf "%.1f" f)
    else Buffer.add_string b (Printf.sprintf "%.6g" f)
  | Str s -> Buffer.add_char b '"'; Buffer.add_string b (escape s); Buffer.add_char b '"'
  | List l ->
    Buffer.add_char b '[';
    List.iteri (fun i x -> if i > 0 then Buffer.add_char b ','; write b x) l;
    Buffer.add_char b ']'
  | Obj kvs ->
    Buffer.add_char b '{';
    List.iteri
      (fun i (k, v) ->
        if i > 0 then Buffer.add_char b ',';
        Buffer.add_char b '"'; Buffer.add_string b (escape k); Buffer.add_string b "\":";
        write b v)
      kvs;
    Buffer.add_char b '}'

let to_string (j : t) : string =
  let b = Buffer.create 1024 in
  write b j;
  Buffer.contents b
