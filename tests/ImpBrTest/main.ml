open CTreeDefinitions;;
open ExtrOcamlIntConv;;
open ImpBrEx;;
open Printf;;

let rec run1 t =
  match observe t with
  | RetF r -> print_int (int_of_nat r)
  | VisF (_e, _k) -> failwith "Vis (unreachable)"
  | BrF (_, k) -> run1 (k (Obj.magic Random.bool()))
  | GuardF t -> run1 t
  | StuckF -> failwith "Stuck"
  | _ -> failwith "unreachable";;

let rec run t =
  match observe t with
  | RetF r -> print_int (int_of_nat r); true
  | VisF (_e, _k) -> failwith "Vis (unreachable)"
  | BrF (_, k) ->
    let b = Random.bool() in
    if run (k (Obj.magic b)) then true else run (k (Obj.magic (not b)))
  | GuardF t -> run t
  | StuckF -> false
  | _ -> failwith "unreachable";;

let rec collect t =
  match observe t with
  | RetF r -> [int_of_nat r]
  | VisF (_e, _k) -> failwith "Vis (unreachable)"
  | GuardF t -> collect t
  | StuckF -> []
  | BrF (_, k) ->
    collect (k (Obj.magic true)) @ collect (k (Obj.magic false))
  | _ -> failwith "unreachable";;

Random.self_init ();;
print_string "Possible return values:";;
let results = collect (Obj.magic ex_prog');;
List.iter (printf " %d") results;;
print_string "\nRandom execution (naïve): ";;
try run1 (Obj.magic ex_prog') with
| _ -> print_string "stuck";;
print_string "\nRandom execution: ";;
run (Obj.magic ex_prog');;
print_newline ()
