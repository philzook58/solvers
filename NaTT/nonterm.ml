open Util
open Params
open Term
open Trs
open Dp
open Io

let put_dp i l r =
	put_term l << puts "\t-#" << put_int i << puts "->" << endl << put_term r

let put_chain (dg : dg) u loop pr =
	let rec sub pos =
		function
		| [] -> ()
		| [i] ->
			let dp = dg#find_dp i in
			let v = string_of_int pos in
			let l = u#subst (Subst.vrename v dp#l) in
			pr#puts "\t--->*";
			pr#endl;
			put_term l pr;
		| i::is ->
			let dp = dg#find_dp i in
			let v = string_of_int pos in
			let l = u#subst (Subst.vrename v dp#l) in
			let r = u#subst (Subst.vrename v dp#r) in
			pr#puts "\t--->*";
			pr#endl;
			put_dp i l r pr;
			sub (pos+1) is;
	in
	sub 1 loop

let estimate_paths len (trs : trs) (dg : dg) scc =
	let subdg = dg#get_subdg scc in
	let rec sub n i k =
		if n > len then []
		else if n = len then
			if i = k then [[]] else []
		else
			Dp.SubDG.fold_succ
			(fun j paths ->
				let folder paths path =
					if List.mem j path then paths else (j::path) :: paths
				in
				List.fold_left folder paths (sub (n+1) j k)
			)
			subdg i []
	in
	sub 0

let find_loop lim (trs : trs) (estimator : Estimator.t) (dg : dg) scc =
	let iterer len nlim i1 =
		let dp1 = dg#find_dp i1 in
		let rec sub pos loop u1 l2 r2 path strict =
			match path with
			| [] ->
				begin
					let l1 = u1#subst dp1#l in
					let r1 = u1#subst dp1#r in
					let l2 = u1#subst l2 in
					let put_loop =
						endl << put_dp i1 l1 r1 << put_chain dg u1 loop
					in
					match Subst.matches l2 l1 with
					| Some(u2) ->
						let print_real_loop =
							enter 2 <<
							put_loop << endl <<
							puts "Looping with: " <<
							u2#output <<
							leave 2
						in
						if strict then begin
							comment (puts " found.");
							proof print_real_loop;
							log (leave 2);
							comment endl;
							raise Nonterm;
						end else begin
							let l3 = u2#subst l2 in
							if duplicating l1 l3 then begin
								comment (puts " found duplicating loop.");
								proof print_real_loop;
								log (leave 2);
								comment endl;
								raise Nonterm;
							end else begin
								debug (print_real_loop << puts "... only weak rules.");
							end;
						end;
					| _ ->
						debug (enter 2 << put_loop << leave 2 << endl << puts "... not looping.");
				end
			| i3::rest ->
				let dp3 = dg#find_dp i3 in
				let v = string_of_int pos in
				let l3 = Subst.vrename v dp3#l in
				let r3 = Subst.vrename v dp3#r in
				let iterer (c2,u2) =
					sub (pos + 1) loop (u1#compose u2) (u2#subst l3) (u2#subst r3) rest
					(strict || dp3#is_strict)
				in
				List.iter iterer (estimator#instantiate_path nlim r2 l3);
		in
		let iterer2 loop =
			log (fun pr ->
				pr#enter 2;
				pr#endl;
				pr#puts "Checking loop: #";
				pr#put_int i1;
				List.iter (fun i -> pr#puts " -> #"; pr#put_int i;) loop;
				pr#flush;
			);
			sub 1 loop (new Subst.t) dp1#l dp1#r loop dp1#is_strict;
			log (leave 2);
		in
		List.iter iterer2 (estimate_paths len trs dg scc i1 i1);
	in
	if lim > 0 then begin
		comment (puts "Finding a loop... " << flush);
		for len = 1 to lim do
			List.iter (iterer len (max 0 (params.max_narrowing - List.length scc))) scc;
		done;
		comment (puts " failed." << endl);

	end
