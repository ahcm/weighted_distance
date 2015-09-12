(**
written by Andreas Hauser <andy@splashground.de>
 
This program computes the distance of two strings. It works
like levenshtein distance with the followingmodifications:
 - The weights depend on the symbol and are floats. Usually
   computed from probabilities.
 - The symbols are not only single characters, but substrings.
 
 
Lizenz:

Creative Commons Deed

Namensnennung-Weitergabe unter gleichen Bedingungen 2.0 Deutschland

Sie dürfen:

    * den Inhalt vervielfältigen, verbreiten und öffentlich aufführen
    * Bearbeitungen anfertigen
    * den Inhalt kommerziell nutzen

Zu den folgenden Bedingungen:
by      Namensnennung. Sie müssen den Namen des Autors/Rechtsinhabers nennen.
sa      Weitergabe unter gleichen Bedingungen. Wenn Sie diesen Inhalt
        bearbeiten oder in anderer Weise umgestalten, verändern oder als
        Grundlage für einen anderen Inhalt verwenden, dann dürfen Sie den
        neu entstandenen Inhalt nur unter Verwendung identischer Lizenzbedingungen
        weitergeben.

    * Im Falle einer Verbreitung müssen Sie anderen die Lizenzbedingungen,
       unter die dieser Inhalt fällt, mitteilen.
    * Jede dieser Bedingungen kann nach schriftlicher Einwilligung des
       Rechtsinhabers aufgehoben werden.

Die gesetzlichen Schranken des Urheberrechts bleiben hiervon unberührt.

Das Commons Deed ist eine Zusammenfassung des Lizenzvertrags in allgemeinverständlicher Sprache. 
Ausführliche Version:
http://creativecommons.org/licenses/by-sa/2.0/de/legalcode
*)

module StringSet =
    Set.Make(
      struct
        type t = string * float
        let compare (s1,f1) (s2, f2) = String.compare s1 s2
      end) 

let cost_table	= Hashtbl.create 50000
let default_cost	= ref 20.0
and cost_table_filename	= ref ""
and max_substring	= ref 1
and use_cost_table	= ref false
and fromfile	= ref false
and measure	= ref false
and tsvfile	= ref false
and show_chars	= ref false
and ignore_case	= ref false
and length	= ref false
(*
let cost_table_add s f =
  StringSet.add (s,f)

let cost_table_get s =
  StringSet.get s
*)

let cost_table_add s f = Hashtbl.add cost_table s f

(** Tab seperated file with substring costs *)
let read_cost_table filename =
  let scan_buf = Scanf.Scanning.from_file filename in
  let add_to_hash freq op =
    let freq_f = float_of_string freq in
    cost_table_add op freq_f in
  let scanf () = Scanf.bscanf scan_buf "%[^\t]\t%[^\n]\n" add_to_hash in
  try
    while true do
        scanf ()
    done
  with
  | End_of_file           -> ()
  | Scanf.Scan_failure(f) -> Printf.printf "Error: %s\n" f; exit 1
  


(** See Brill and Moore, 2000, for the inspiration of this modified levenshtein *)
let frequency_weighted_distance s1 s2  =
  let s1 = "^" ^ s1 ^ "$" in 
  let s2 = "^" ^ s2 ^ "$" in 
  let default_cost = !default_cost in
  let l1 = String.length s1 in
  let l2 = String.length s2 in
  let table = Array.make_matrix (l1 + 1) (l2 + 1) infinity in
  let table_set x y v = table.(x).(y) <- v in
  let table_get x y = table.(x).(y) in
  let conversions_table = Array.make_matrix (l1 + 1) (l2 + 1) "" in
  let max_substring = !max_substring in
  (** Find the minimum cost to x y allowing for conversions
      of the set of substrings before x in string 1 to
      the set of substrings before y in string 2 with
      maximum substring length of max_substring.
      E.g.:
        string 1 = "abcd"
        string 2 = "abxy"
        x = 3
        y = 3
          "d" > "y"
          "d" > "xy"
          "d" > "bxy"

         "cd" > "y"
         "cd" > "xy"
         "cd" > "bxy"

        "bcd" > "y"
        "bcd" > "xy"
        "bcd" > "bxy"
        *)
  let get_minimum minimum_cost x y =
    let minimum = ref minimum_cost in
    let min_x = min max_substring x in
    let min_y = min max_substring y in
    for i = 0 to min_x do
      let substr_x = String.sub s1 (x - i) i in
      for j = 0 to min_y do
        if i <> 0 && j <> 0 then 
          begin
            let substr_y = String.sub s2 (y - j) j in
            if substr_x <> substr_y then
              begin
                let s = substr_x ^ ">" ^ substr_y in
                if Hashtbl.mem cost_table s then
                  let c = (table_get (x - i) (y - j)) +. (Hashtbl.find cost_table s) in
                  if c < !minimum then
                      minimum := c;
              end
            else
              let c = table_get (x - i) (y - j) in
              if c < !minimum then
                minimum := c;
          end
      done;
    done;
    !minimum
  in
  let get_minimum_with_c minimum_cost default_conv_str x y =
    let conv_str = ref default_conv_str in
    let minimum = ref minimum_cost in
    let min_x = min max_substring x in
    let min_y = min max_substring y in
    for i = 0 to min_x do
      let substr_x = String.sub s1 (x - i) i in
      for j = 0 to min_y do
          begin
            let substr_y = String.sub s2 (y - j) j in
            if substr_x = substr_y then
              begin
                let c = table_get (x - i) (y - j) in
                if c < !minimum then
                  begin
                    minimum := c;
                    conv_str := (conversions_table.(x - i).(y - j) ^ " " ^ (substr_x ^ ">" ^ substr_y))
                  end
              end
            else
              let s = substr_x ^ ">" ^ substr_y in
              if Hashtbl.mem cost_table s then
                let c = (table_get (x - i) (y - j)) +. (Hashtbl.find cost_table s) in
                if c < !minimum then
                  begin
                    minimum := c;
                    conv_str := (conversions_table.(x - i).(y - j) ^ " " ^ s)
                  end
          end
      done;
    done;
    (!minimum, !conv_str)
  in
  let table_set_min_with_c minimum_cost default_conv_str x y =
    let (cost,conv) = get_minimum_with_c minimum_cost default_conv_str x y in
    if cost < (table_get x y) then
      begin
        conversions_table.(x).(y) <- conv;
        table_set x y cost
      end
  in
  let table_set_min minimum_cost x y =
    let cost = get_minimum minimum_cost x y in
    if cost < (table_get x y) then
      table_set x y cost
  in
  (** levenshtein distance, cost matrix without dijkstra *)
  let distance () =
    for x = 1 to (l1 - 2) do
      for y = 1 to (l2 - 2) do
        let current_cost = (table_get x y) +. default_cost in
        table_set_min current_cost (x + 1)  y;
        table_set_min current_cost  x      (y + 1);
        table_set_min current_cost (x + 1) (y + 1)
      done
    done
  in
  (** Same but records the char conversions *)
  let distance_with_c () =
    for x = 1 to (l1 - 2) do
      for y = 1 to (l2 - 2) do
        let current_str  = conversions_table.(x).(y) ^ " " in
        let current_cost = (table_get x y) +. default_cost in
        flush_all ();
        let s1x1 = "" in
        let s1x2 = String.sub s1 x 1 in
        let s2y1 = "" in
        let s2y2 = String.sub s2 y 1 in
        table_set_min_with_c current_cost (current_str ^ s1x2 ^ ">" ^ s2y1) (x + 1)  y;
        table_set_min_with_c current_cost (current_str ^ s1x1 ^ ">" ^ s2y2)  x      (y + 1);
        table_set_min_with_c current_cost (current_str ^ s1x2 ^ ">" ^ s2y2) (x + 1) (y + 1)
      done
    done
  in
  table_set 1 1 0.0;
  if !show_chars then
    begin
      distance_with_c ();
      Printf.printf "%s " conversions_table.(l1 - 1).(l2 - 1);
      Printf.printf "|";
      table_get (l1 - 1) (l2 - 1)
    end
  else
    begin
      if s1 = s2 then
        0.0
      else
        begin
          distance ();
          table_get (l1 - 1) (l2 - 1)
        end
    end

open Printf

let do_search pattern s =
  let pattern = if !ignore_case then String.lowercase pattern else pattern in
  let matched a b = if b = pattern || a = pattern then 1 else 0 in
  let print_dist a b =
    let a = if !ignore_case then String.lowercase a else a in
    let b = if !ignore_case then String.lowercase b else b in
    let length_adjust dist a b =
      if !length then
        dist /. float_of_int (String.length a + String.length b)
      else
        dist
    in
    if !measure then
      printf "%f\t%s\t%s\t%s\t%d\n" (length_adjust (frequency_weighted_distance pattern a) pattern a) a b pattern (matched a b)
    else
      printf "%f\t%s\t%s\n" (length_adjust (frequency_weighted_distance a b ) a b)a b
      (*
    else if !measure && not !fromfile then
      let print_dist2 dist = 
        if !length then
          printf "%f\t%s\t%s\t%s\t%d\n" (wrt_length dist a b) a b pattern (matched a b)
        else
          printf "%d\t%s\t%s\t%s\t%d\n" (int_of_float dist) a b pattern (matched a b)
      in
        print_dist2 (float_of_int (weighted_distance lc pattern a))
    else
      let dist = if !show_chars then char_difference lc a b else weighted_distance lc a b in
      if !length then
        printf "%f\t%s\t%s\n" (wrt_length (float_of_int dist) a b)  a b
      else
        printf "%d\t%s\t%s\n" dist a b
        *)
  in
  if !use_cost_table then read_cost_table !cost_table_filename;
  if !tsvfile or !fromfile or !measure then
    let filename = s in
    let scan_buf = Scanf.Scanning.from_file filename in
    let ic       = open_in s in
    let scanf () =
      if !tsvfile && not !measure then
        Scanf.bscanf scan_buf "%s\t%s\n" print_dist
      else
        if !fromfile then
          Scanf.bscanf scan_buf "%s\n" print_dist pattern
        else
          Scanf.bscanf scan_buf "%[^\t]\t%[^\n]\n" print_dist
    in
    while true do
      try
        scanf ();
        flush_all()
      with
      | End_of_file           -> close_in ic; exit 0
      | Scanf.Scan_failure(f) -> printf "Error: %s\n" f ; exit 1
    done
  else
    print_dist pattern s

let _ =
  let pattern = ref None in
  Arg.parse
    ["-i", Arg.Set ignore_case, "  ignore case";
     "-d", Arg.Float(fun f -> default_cost := f), "<f>  default costs of float f for -h";
     "-n", Arg.Int(fun n -> max_substring := n), "<n>  max substring context";
     "-f", Arg.Set fromfile,  "  search in given file rather than in string";
     "-t", Arg.Set tsvfile,   "  search in given file, two strings tab seperated";
     "-l", Arg.Set length,   "  distance / (length(a) + length(b))";
     "-h", Arg.String(fun f -> cost_table_filename := f; use_cost_table := true), "frequency table to read weights from";
     "-v", Arg.Set show_chars,   "  display the characters that need to be changed";
     "-m", Arg.Set measure,   "  measure a pattern and a file, two strings tab seperated"]
    (fun s ->
      match !pattern with
        None   ->
          begin
          if !tsvfile && not !measure then
            do_search "" s
          else
            pattern := Some(s);
          end
      | Some p -> do_search p s)
    "Usage: weigthed_distance [options] [<pattern>] [<string> | <filename>]\nOptions are:"
