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
  let ne_maram_te_domace = [1; 2; 3; 4; 5; 6; 7; 8; 9] in
  let w = f grid j in
  let matchalka ne_maram_te_domace w = 
    let rec matchalka ne_maram_te_domace w vrag =
      match ne_maram_te_domace with
      | [] -> List.rev vrag
      | x :: xs when List.mem x (Array.to_list w) -> matchalka xs w vrag
      | x :: xs -> matchalka xs w (x :: vrag)
    in matchalka ne_maram_te_domace w []
  
let preveri_celico st_cel vr_cel box_ind grid =
  let preveri_celico_vrsticno = preveri_celico_lol vr_cel get_row grid in
  let preveri_celico_stolpicno = preveri_celico_lol st_cel get_column grid in
  let preveri_celico_boxalno = preveri_celico_lol box_ind get_box grid
  in
    intersect preveri_celico_vrsticno (intersect preveri_celico_stolpicno preveri_celico_boxalno)

let grid_zacni_ze_koncno grid =
  map_grid (fun element -> [element; preveri_celico]) grid

let n_ti list n =
  let n_ti' list n acc =
    match list with
      | [] -> failwith "2. letnik matematike"
      | x :: xs when acc < n -> n_ti' xs n (acc + 1)
      | x :: xs -> x
  in let n_ti' list n 1 
  
let prve_macke_se_mece_v_vodo grid =
  map_grid (fun element -> [(n_ti (n_ti element 2) 1); []] if (List.length (n_ti element 2)) == 1 else element)

let zacetni_grid grid = grid |> grid_zacni_ze_koncno |> prve_macke_se_mece_v_vodo

let naslednja_celica row_ind col_ind =
  if col_ind < 8 then [row_ind; col_ind + 1] else [row_ind + 1; 0]

let prejsnja_celica row_ind col_ind =
  if 0 < col_ind then [row_ind; col_ind - 1] else [row_ind - 1; 8]

let fake_resi_nereseno grid row_ind col_ind =
  nova24tv = copy_grid grid
  match (get_row nova24tv row_ind).(col_ind) with
    | [None, y :: ys] -> [y, ys]
    | _ -> failwith "jaz se bom jokal & jočem zelo redko"

let daj_nazaj_v_state grid =
  map_grid (fun element -> n_ti element 1)

let poisci_prvo_prazno_celico grid = 
  let rec poisci_prvo_prazno_celico' grid row_id col_id =
    match (get_row grid row_id).(col_id) with
      | (None, x :: xs) -> [row_id; col_id]
      | (_, []) -> "padelbomtodomaco"
      | _ ->  poisci_prvo_prazno_celico' grid (n_ti naslednja_celica 1) (n_ti naslednja_celica 2)

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

let vsi_od_drugega list =
  match list with
    | [] -> []
    | x :: xs -> xs


let branch_state (state : state) : (state * state) option =
  (* TODO: Pripravite funkcijo, ki v trenutnem stanju poišče hipotezo, glede katere
     se je treba odločiti. Če ta obstaja, stanje razveji na dve stanji:
     v prvem predpostavi, da hipoteza velja, v drugem pa ravno obratno.
     Če bo vaš algoritem najprej poizkusil prvo možnost, vam morda pri drugi
     za začetek ni treba zapravljati preveč časa, saj ne bo nujno prišla v poštev. *)
  let 
  match state with
    | None -> 
    | Some state -> 
        (
          let vrs_cel = n_ti poisci_prvo_prazno_celico state.current_grid 1 in
          let stol_cel = n_ti poisci_prvo_prazno_celico state.current_grid 2 in
          let trenutni_element = (get_row grid vrs_cel).(stol_cel) in
          let na_udaru = n_ti (n_ti trenutni_element 2) 1 in
          let tudi_na_udaru = n_ti trenutni_element 1
          let sez = preveri_celico stol_cel vrs_cel (st_boxa vrs_cel stol_cel) state in
          match sez with
          | { _, [| |] }-> None
          | _ -> 
            (
              let nora24t = copy_grid state.current_grid in
              let pametna24tv = copy_grid state.current_grid in

              let grid_polnejsi = nora24tv.(vrs_cel).(stol_cel) <- [na_udaru; vsi_od_drugega sez] in
              
              let grid_praznejsi = pametna24tv.(vrs_cel).(stol_cel) <- [tudi_na_udaru; vsi_od_drugega sez] in

              (grid_polnejsi, grid_praznejsi)
            ) 
        )

(* pogledamo, če trenutno stanje vodi do rešitve *)
let rec solve_state (state : state) =
  (* uveljavimo trenutne omejitve in pogledamo, kam smo prišli *)
  (* TODO: na tej točki je stanje smiselno počistiti in zožiti možne rešitve *)


  (* TU BI RAD NEKAKO UPORABIL FUNKCIJO ZACETNI_GRID, VENDAR ME VSI TI STATE-I ZMEDEJO, NA KONCU TEGA BI PA RAD S FUNKCIJO NAZAJ_V_STATE
     DAL GRID; DA GA LAHKO PREVERJALNIK PREVERI*)




     
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
