type available = { loc : int * int; possible : int list }

(* TODO: tip stanja ustrezno popravite, saj boste med reševanjem zaradi učinkovitosti
   želeli imeti še kakšno dodatno informacijo *)
type state = { problem : Model.problem; current_grid : int option Model.grid }

let print_state (state : state) : unit =
  Model.print_grid
    (function None -> "?" | Some digit -> string_of_int digit)
    state.current_grid

type response = Solved of Model.solution | Unsolved of state | Fail of state

let initialize_state (problem : Model.problem) : state =
  { current_grid = Model.copy_grid problem.initial_grid; problem }
  
let st_boxa row_id col_id =
  match col_id, row_id with
    | a, b when a <= 2 && b <= 2 -> 0
    | a, b when a <= 5 && a >= 3 && b <= 2 -> 1
    | a, b when a >= 6 && b <= 2 -> 2
    | a, b when a <= 2 && b <= 5 && b >= 3 -> 3
    | a, b when a <= 5 && a >= 3 && b <= 5 && b >= 3 -> 4
    | a, b when a >= 6 && b <= 5 && b >= 3 -> 5
    | a, b when a <= 2 && b >= 6 -> 6
    | a, b when a >= 3 && a <= 5 && b >= 6 -> 7
    | a, b when a >= 6 && b >= 6 -> 8
    | _ -> failwith "ojoj"

let validate_state (state : state) : response =
  let unsolved =
    Array.exists (Array.exists Option.is_none) state.current_grid
  in
  if unsolved then Unsolved state
  else
    (* Option.get ne bo sprožil izjeme, ker so vse vrednosti v mreži oblike Some x *)
    let solution = Model.map_grid Option.get state.current_grid in
    if Model.is_valid_solution state.problem solution then Solved solution
    else Fail state

let rec intersect l1 l2 =
  match l1 with 
      | [] -> []
      | h1::t1 -> (
        match l2 with 
            | [] -> []
            | h2::t2 when h1 < h2 -> intersect t1 l2
            | h2::t2 when h1 > h2 -> intersect l1 t2
            | h2::t2 -> (
              match intersect t1 t2 with 
                  | [] -> [h1]
                  | h3::t3 as l when h3 = h1 -> l
                  | h3::t3 as l -> h1::l
            )
      )

let preveri_celico_lol j f grid =
  let zacetna = [1; 2; 3; 4; 5; 6; 7; 8; 9] in
  let w = f grid j in
  let matchalka zacetna w =
    let rec matchalka' zacetna w acc =
      match zacetna with
      | [] -> List.rev acc
      | x :: xs when List.mem x (Array.to_list w) -> matchalka' xs w acc
      | x :: xs -> matchalka' xs w (x :: acc)
    in matchalka' zacetna w []
  in matchalka zacetna w
  
let preveri_celico st_cel vr_cel box_ind grid =
  let preveri_celico_vrsticno = preveri_celico_lol vr_cel Model.get_row grid in
  let preveri_celico_stolpicno = preveri_celico_lol st_cel Model.get_column grid in
  let preveri_celico_boxalno = preveri_celico_lol box_ind Model.get_box grid
  in
    intersect preveri_celico_vrsticno (intersect preveri_celico_stolpicno preveri_celico_boxalno)

let grid_zacni_ze_koncno grid =
  (* Model.map_grid (fun element -> [element; preveri_celico st_cel vr_cel (st_boxa vr_cel st_cel) grid]) grid *)
  Array.init 9 (fun i -> Array.init 9 (fun j -> (grid.(i).(j), preveri_celico j i (st_boxa i j) grid)))

let n_ti list n =
  let rec n_ti' list n acc =
    match list with
      | [] -> failwith "2. letnik matematike"
      | x :: xs when acc < n -> n_ti' xs n (acc + 1)
      | x :: xs -> x
  in n_ti' list n 1 

let pameten_zacetek grid =
  Model.map_grid (fun element -> let (x, y) = element in if (List.length y) == 1 then (n_ti y 1, []) else element)

let zacetni_grid grid = grid |> grid_zacni_ze_koncno |> pameten_zacetek

let naslednja_celica row_ind col_ind =
  if col_ind < 8 then (row_ind, col_ind + 1) else (row_ind + 1, 0)

let prejsnja_celica row_ind col_ind =
  if 0 < col_ind then (row_ind, col_ind - 1) else (row_ind - 1, 8)

let vsi_od_drugega list =
  match list with
    | [] -> []
    | x :: xs -> xs

let fake_resi_nereseno grid row_ind col_ind =
  match grid.(row_ind).(col_ind) with
    | (None, Some list) -> (n_ti list 1, vsi_od_drugega list)
    | _ -> failwith "jaz se bom jokal & jočem zelo redko"

let daj_nazaj_v_state grid =
  Model.map_grid (fun element -> n_ti element 1)

let poisci_prvo_prazno_celico grid = 
  let rec poisci_prvo_prazno_celico' grid row_id col_id =
    let (x, y) = naslednja_celica row_id col_id in
    match grid.(row_id).(col_id) with
      | (None, Some list) -> (row_id, col_id)
      | (_, Some []) -> failwith "padelbomtodomaco"
      | _ -> poisci_prvo_prazno_celico' grid x y
  in poisci_prvo_prazno_celico' grid 0 0



let branch_state (state : state) : (state * state) option =
  (* TODO: Pripravite funkcijo, ki v trenutnem stanju poišče hipotezo, glede katere
     se je treba odločiti. Če ta obstaja, stanje razveji na dve stanji:
     v prvem predpostavi, da hipoteza velja, v drugem pa ravno obratno.
     Če bo vaš algoritem najprej poizkusil prvo možnost, vam morda pri drugi
     za začetek ni treba zapravljati preveč časa, saj ne bo nujno prišla v poštev. *)
          let griid = grid_zacni_ze_koncno state.current_grid in
          let vrs_cel = n_ti poisci_prvo_prazno_celico griid 1 in
          let stol_cel = n_ti poisci_prvo_prazno_celico griid 2 in
          let trenutni_element = (Model.get_row grid vrs_cel).(stol_cel) in
          let na_udaru = n_ti (n_ti trenutni_element 2) 1 in
          let tudi_na_udaru = n_ti trenutni_element 1 in
          let sez = preveri_celico stol_cel vrs_cel (st_boxa vrs_cel stol_cel) griid in
          match sez with
            | [] -> None
            | _ -> 
              (
                let nova_kopija = copy_grid griid in
                let noova_kopija = copy_grid griid in

                let grid_polnejsi = nova_kopija.(vrs_cel).(stol_cel) <- (na_udaru, vsi_od_drugega sez) in
                let grid_praznejsi = noova_kopija.(vrs_cel).(stol_cel) <- (tudi_na_udaru, vsi_od_drugega sez) in

                let grid_polnejsi' = daj_nazaj_v_state grid_polnejsi in
                let grid_praznejsi' = daj_nazaj_v_state grid_praznejsi in

                (grid_polnejsi', grid_praznejsi')
              ) 

(* pogledamo, če trenutno stanje vodi do rešitve *)
let rec solve_state (state : state) =
  (* uveljavimo trenutne omejitve in pogledamo, kam smo prišli *)
  (* TODO: na tej točki je stanje smiselno počistiti in zožiti možne rešitve *)

  match validate_state state with
  | Solved solution ->
      (* če smo našli rešitev, končamo *)
      Some solution
  | Fail fail ->
      (* prav tako končamo, če smo odkrili, da rešitev ni *)
      None
  | Unsolved state' ->
      (* če še nismo končali, raziščemo stanje, v katerem smo končali *)
      explore_state state'

and explore_state (state : state) =
  (* pri raziskovanju najprej pogledamo, ali lahko trenutno stanje razvejimo *)
  match branch_state state with
  | None ->
      (* če stanja ne moremo razvejiti, ga ne moremo raziskati *)
      None
  | Some (st1, st2) -> (
      (* če stanje lahko razvejimo na dve možnosti, poizkusimo prvo *)
      match solve_state st1 with
      | Some solution ->
          (* če prva možnost vodi do rešitve, do nje vodi tudi prvotno stanje *)
          Some solution
      | None ->
          (* če prva možnost ne vodi do rešitve, raziščemo še drugo možnost *)
          solve_state st2 )

let solve_problem (problem : Model.problem) =
  problem |> initialize_state |> solve_state
