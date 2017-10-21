

open Core

type opcode = DUP | DROP | SWAP | CDR | CAR | PUSH | POP | PAIR | UNPAIR | UNPIAR
type values = Var of string | Pair of values * values
type stack = Invalid | Stack of (values list) * (values list)
                 
let rec run = function
  | ( [ ], s) -> s
  | (   DUP::code, Stack          (h::s, r)) -> run (code, Stack (h::h::s, r))
  | (  DROP::code, Stack          (h::s, r)) -> run (code, Stack (s,       r))
  | (  SWAP::code, Stack       (a::b::s, r)) -> run (code, Stack (b::a::s, r))
  | (   CAR::code, Stack (Pair (a,b)::s, r)) -> run (code, Stack (a::s,    r))
  | (   CDR::code, Stack (Pair (a,b)::s, r)) -> run (code, Stack (b::s,    r))
  | (   POP::code, Stack          (h::s, r)) -> run (code, Stack (s,    h::r))
  | (  PUSH::code, Stack          (s, h::r)) -> run (code, Stack (h::s,    r))
  | (  PAIR::code, Stack  (a::b::s,      r)) -> run (code, Stack ((Pair (a,b))::s, r))
  | (UNPAIR::code, Stack  (Pair (a,b)::s,r)) -> run (code, Stack(a::b::s, r))
  | (UNPIAR::code, Stack  (Pair (a,b)::s,r)) -> run (code, Stack(b::a::s, r))
  | ( _          ,                      _  ) -> Invalid

let rec opcost = function
  | UNPAIR -> 4 (* DUP; CDR; SWAP; CAR *)
  | UNPIAR -> 4 (* DUP; CAR; SWAP; CDR *)
  | _ -> 1


type solution = {mutable cost : float; mutable code : opcode list}

module IntSet = Set.Make(struct type t = string let compare = compare end)

let rec list_variables = function
  | Stack ((Var a)::s, r)       -> a::(list_variables (Stack (s,r)))
  | Stack ((Pair (a,b))::s, r)  -> list_variables (Stack (a::b::s,r))
  | Stack ([], (Var a)::r)      -> a::(list_variables (Stack ([],r)))
  | Stack ([], (Pair (a,b))::r) -> list_variables (Stack ([],a::b::r))
  | _ -> []

let present_variables x = IntSet.of_list (list_variables x)
let variables_str x = String.concat "" (list_variables x)

(* adapted from https://ocaml.janestreet.com/ocaml-core/109.31.00/doc/core_extended/Extended_string.html *)

let edit_distance_matrix s1 s2 =
  let l1, l2 = String.length s1, String.length s2 in
  let d = Array.make_matrix (l1+1) (l2+1) 0 in
  for x=0 to l1 do d.(x).(0) <- x done;
  for y=0 to l2 do d.(0).(y) <- y done;
  for y=1 to l2 do
    for x=1 to l1 do
      let min_d =
        if s1.[x-1] = s2.[y-1] then d.(x-1).(y-1)
        else List.reduce_exn ~f:min
          [d.(x-1).(y) + 1;
           d.(x).(y-1) + 1;
           d.(x-1).(y-1) + 1]
      in
      let min_d =
        if x > 1 && y > 1
          && s1.[x-1] = s2.[y-2] && s1.[x-2] = s2.[y-1]
        then min min_d (d.(x-2).(y-2) + 1)
        else min_d
      in
      d.(x).(y) <- min_d
    done;
  done;
  d

let edit_distance s1 s2 =
  (edit_distance_matrix s1 s2).(String.length s1).(String.length s2)

(* An admissible heuristic for the cost of reaching sb from sa.
   It must always underestimate the cost
*)
let heuristic sa sb =
  (* rules:
     a) each pair that needs to be destructured takes at least one op
     b) each pair that needs to be formed takes at least one op
     c) if some variables are missing, we're doomed to fail
     d) if we have extra variables, they'll take at least one op to get rid of
     e) drop should never follow dup
     f) invalid stacks are irrecoverable
  *)
  let maxint = 10000 in
  (* rule f *)
  if sa = Invalid then
    maxint
  else begin
    (* rule a *)
    let varB = present_variables sb and varA =  present_variables sa in
    if not IntSet.(diff varB varA |> is_empty) then
      maxint
    else 
      let n  = edit_distance (variables_str sb) (variables_str sa) in n
  end
        
let optimize sa sb =
  let nodes = Heap.one sa (0 + heuristic sa sb, 0, []) in
  let rec optimize_aux () =
    if Heap.size nodes <= 0 then
      None
    else begin
      let (s, (cost, total, code)) = Heap.pop nodes in
      if s = sb then
        Some (cost, List.rev code)
      else begin
        List.iter
          (fun opcode -> let sa = (run ([opcode], s)) and
            newcost = opcost opcode + cost in
            let v = (newcost + heuristic sa sb, newcost, opcode::code) in
            if Heap.mem nodes sa then
              Heap.decrease nodes sa v
            else
              Heap.insert nodes sa v
          )
          [DUP; DROP; SWAP; CDR; CAR; PUSH; POP; PAIR; UNPAIR; UNPIAR];
        optimize_aux ()
      end
    end
  in optimize_aux ()


(** Example *)

let example = function () ->
let a = Var "a" and b = Var "b" and c = Var "c" in
let start = Stack ([Pair (a, b); c], []) and target = Stack ([Pair (c,a); b], []) in
optimize start target
  
