module Blake2
#set-options "--z3rlimit 20 --max_fuel 0"
open Spec.Lib.IntTypes
open Spec.Lib.RawIntTypes
open Spec.Lib.IntSeq
open Speclib


let variant = x:nat{(x = 0x0) || (x = 0x1)}
let index_t = range_t 0x0 0x10
(*
(* Having all the numbers written in hex lessens readability of the F* spec *)
let _SIGMA : array_t index_t (0x10 *. (* Wrong multiplication here, nat/uint*) 0xc)  = let l_ = [ 0x0; 0x1; 0x2; 0x3; 0x4; 0x5; 0x6; 0x7; 0x8; 0x9; 0xa; 0xb; 0xc; 0xd; 0xe; 0xf; 0xe; 0xa; 0x4; 0x8; 0x9; 0xf; 0xd; 0x6; 0x1; 0xc; 0x0; 0x2; 0xb; 0x7; 0x5; 0x3; 0xb; 0x8; 0xc; 0x0; 0x5; 0x2; 0xf; 0xd; 0xa; 0xe; 0x3; 0x6; 0x7; 0x1; 0x9; 0x4; 0x7; 0x9; 0x3; 0x1; 0xd; 0xc; 0xb; 0xe; 0x2; 0x6; 0x5; 0xa; 0x4; 0x0; 0xf; 0x8; 0x9; 0x0; 0x5; 0x7; 0x2; 0x4; 0xa; 0xf; 0xe; 0x1; 0xb; 0xc; 0x6; 0x8; 0x3; 0xd; 0x2; 0xc; 0x6; 0xa; 0x0; 0xb; 0x8; 0x3; 0x4; 0xd; 0x7; 0x5; 0xf; 0xe; 0x1; 0x9; 0xc; 0x5; 0x1; 0xf; 0xe; 0xd; 0x4; 0xa; 0x0; 0x7; 0x6; 0x3; 0x9; 0x2; 0x8; 0xb; 0xd; 0xb; 0x7; 0xe; 0xc; 0x1; 0x3; 0x9; 0x5; 0x0; 0xf; 0x4; 0x8; 0x6; 0x2; 0xa; 0x6; 0xf; 0xe; 0x9; 0xb; 0x3; 0x0; 0x8; 0xc; 0x2; 0xd; 0x7; 0x1; 0x4; 0xa; 0x5; 0xa; 0x2; 0x8; 0x4; 0x7; 0x6; 0x1; 0x5; 0xf; 0xb; 0x9; 0xe; 0x3; 0xc; 0xd; 0x0; 0x0; 0x1; 0x2; 0x3; 0x4; 0x5; 0x6; 0x7; 0x8; 0x9; 0xa; 0xb; 0xc; 0xd; 0xe; 0xf; 0xe; 0xa; 0x4; 0x8; 0x9; 0xf; 0xd; 0x6; 0x1; 0xc; 0x0; 0x2; 0xb; 0x7; 0x5; 0x3 ] in
                                             assert_norm(List.Tot.length l_ == 192);
                                             createL l_
*)
let highbits_128 (x:uint128_t)  (* Inferred type should not be None *) =
  (* nat/uint mismatch, should generate to_u64 *) to_u64 (x >>. (* The shift val should be a uint32_t *) (u32 0x40))
let highbits_64 (x:uint64_t)  =
  to_u32 (x >>. (u32 0x20))
let word_t (v:variant) =
  let ty = if ((v = 0x0)) then (let ty = uint64_t in ty )else (let ty = uint32_t in ty) in
  ty

(* We need to add this function, to have access the the inttype variants and not only the types for annotations *)
let word_v (v:variant) =
 if v = 0 then U64 else U32
let double_word_t (v:variant) =
  let ty = if ((v = 0x0)) then (let ty = uint128_t in ty )else (let ty = uint64_t in ty) in
  ty
  (*
let word_bits (v:variant) : None =
  let b = if ((v = 0x0)) then (let b = 0x40 in b )else (let b = 0x20 in b) in
  b
let to_word (v:variant) : None =
  let f = if ((v = 0x0)) then (let f = uint64 in f )else (let f = uint32 in f) in
  f
  *)

(*
  You have to write a val here, and specify the lengths of the seqs correctly.
*)
val to_words_le (v:variant) : (s:vlbytes_t{length s % (numbytes (word_v v)) = 0} -> vlarray_t (word_t v))
let to_words_le (v:variant) =
  let f =
    if ((v = 0x0)) then
     (let f = uints_from_bytes_le #U64 in f)
    else
     (let f = uints_from_bytes_le #U32 in f)
  in f

(*
let from_words_le (v:variant) : None =
  let f = if ((v = 0x0)) then (let f = uints_to_bytes_le #U64 in f )else (let f = uints_to_bytes_le #U32 in f) in
  f
let rounds_in_f (v:variant) : None =
  let r = if ((v = 0x0)) then (let r = 0xc in r )else (let r = 0xa in r) in
  r
let block_bytes (v:variant) : None =
  let bb = if ((v = 0x0)) then (let bb = 0x80 in bb )else (let bb = 0x40 in bb) in
  bb
let __R (v:variant) : None  =
  let t = if ((v = 0x0)) then (let t = Tuple(elts=0x20
            0x18
            0x10 (*The tuples are handled poorly here*)
            0x3f,
            ctx=Load()) in t )else (let t = Tuple(elts=0x10
            0xc
            0x8
            0x7,
            ctx=Load()) in t) in
  t
let _IV (v:variant) =
  let iv = if ((v = 0x0)) then (
  let l_ : list uint64_t = [ u64 0x6a09e667f3bcc908; u64 0xbb67ae8584caa73b; u64 0x3c6ef372fe94f82b; u64 0xa54ff53a5f1d36f1; u64 0x510e527fade682d1; u64 0x9b05688c2b3e6c1f; u64 0x1f83d9abfb41bd6b; u64 0x5be0cd19137e2179 ]
  in
             assert_norm(List.Tot.length l_ == 8);
             createL l_)else ((* The nested let ... in seems to confuse F*, especially without type annotations *)let iv = let l_ = [ u32 0x6a09e667; u32 0xbb67ae85; u32 0x3c6ef372; u32 0xa54ff53a; u32 0x510e527f; u32 0x9b05688c; u32 0x1f83d9ab; u32 0x5be0cd19 ] in
             assert_norm(List.Tot.length l_ == 8);
             createL l_ in iv) in
  iv
 *)
(* Same thing, you have to specify that its a function *)
let high_bits (v:variant) : (double_word_t v -> word_t v) =
  let f = if ((v = 0x0)) then (let f = highbits_128 in f )else (let f = highbits_64 in f) in
  f
  (*
let to_double_word (v:variant) : None =
  let f = if ((v = 0x0)) then (let f = uint128 in f )else (let f = uint64 in f) in
  f
let working_vector_t (v:variant) : None =
  array_t (word_t v) 0x10
let hash_vector_t (v:variant) : None =
  array_t (word_t v) 0x8
let max_size_t (v:variant) : None =
  ((0x2 **. word_bits v) -. 0x1)
let minus_one (v:variant) : None =
  to_word v (max_size_t v)
let data_internal_t (v:variant) : None =
  (* The contract objects is not compiled properly *)
  refine bytes_t Lambda(args=arguments(args=arg(arg='x',
  annotation=None,
  type_comment=None),
  vararg=None,
  kwonlyargs=,
  kw_defaults=,
  kwarg=None,
  defaults=),
  body=((length x) < (0x2 **. (word_bits v))) && (((length x) %. (block_bytes v)) = 0x0))
let key_t (v:variant) : None =
  refine vlbytes_t Lambda(args=arguments(args=arg(arg='x',
  annotation=None,
  type_comment=None),
  vararg=None,
  kwonlyargs=,
  kw_defaults=,
  kwarg=None,
  defaults=),
  body=((length x) <= (word_bits v)))
let key_size_t (v:variant) : None =
  refine nat Lambda(args=arguments(args=arg(arg='x',
  annotation=None,
  type_comment=None),
  vararg=None,
  kwonlyargs=,
  kw_defaults=,
  kwarg=None,
  defaults=),
  body=(x <= (word_bits v)))
let out_size_t (v:variant) : None =
  refine nat Lambda(args=arguments(args=arg(arg='x',
  annotation=None,
  type_comment=None),
  vararg=None,
  kwonlyargs=,
  kw_defaults=,
  kwarg=None,
  defaults=),
  body=(x <= (word_bits v)))
let low_bits (v:variant) : None =
  to_word v
let data_t (v:variant) : None =
  refine vlbytes_t Lambda(args=arguments(args=arg(arg='x',
  annotation=None,
  type_comment=None),
  vararg=None,
  kwonlyargs=,
  kw_defaults=,
  kwarg=None,
  defaults=),
  body=((length x) < ((max_size_t v) -. (0x2 *. (block_bytes v)))))
let blake2 (var:variant) : None =
  let __G (v:working_vector_t var) (a:index_t) (b:index_t) (c:index_t) (d:index_t) (x:word_t var) (y:word_t var) : working_vector_t var =
    let (_R1,_R2,_R3,_R4) = __R var in
    let v = v.[a] <- ((v.[a] +. v.[b]) +. x) in
    let v = v.[d] <- word_t var.rotate_right (v.[d] ^. v.[a]) _R1 in
    let v = v.[c] <- (v.[c] +. v.[d]) in
    let v = v.[b] <- word_t var.rotate_right (v.[b] ^. v.[c]) _R2 in
    let v = v.[a] <- ((v.[a] +. v.[b]) +. y) in
    let v = v.[d] <- word_t var.rotate_right (v.[d] ^. v.[a]) _R3 in
    let v = v.[c] <- (v.[c] +. v.[d]) in
    let v = v.[b] <- word_t var.rotate_right (v.[b] ^. v.[c]) _R4 in
    v in
  let __F (h:hash_vector_t var) (m:working_vector_t var) (t:double_word_t var) (flag:bool) : hash_vector_t var =
    let v = create 0x10 (to_word var 0x0) in
    let v = update_slice v 0x0 0x8 h in
    let v = update_slice v 0x8 0x10 (_IV var) in
    let v = v.[0xc] <- (v.[0xc] ^. low_bits var t) in
    let v = v.[0xd] <- (v.[0xd] ^. high_bits var (t >>. 0x40)) in
    let v = if ((flag = True)) then (let v = v.[0xe] <- (v.[0xe] ^. minus_one var) in v )else (v) in
    let (v,s) = repeati (range (rounds_in_f var))
      (fun i (v,s) ->
        let s = slice _SIGMA (i *. 0x10) ((i +. 0x1) *. 0x10) in
        let v = __G v 0x0 0x4 0x8 0xc m.[s.[0x0]] m.[s.[0x1]] in
        let v = __G v 0x1 0x5 0x9 0xd m.[s.[0x2]] m.[s.[0x3]] in
        let v = __G v 0x2 0x6 0xa 0xe m.[s.[0x4]] m.[s.[0x5]] in
        let v = __G v 0x3 0x7 0xb 0xf m.[s.[0x6]] m.[s.[0x7]] in
        let v = __G v 0x0 0x5 0xa 0xf m.[s.[0x8]] m.[s.[0x9]] in
        let v = __G v 0x1 0x6 0xb 0xc m.[s.[0xa]] m.[s.[0xb]] in
        let v = __G v 0x2 0x7 0x8 0xd m.[s.[0xc]] m.[s.[0xd]] in
        let v = __G v 0x3 0x4 0x9 0xe m.[s.[0xe]] m.[s.[0xf]] in
        (v,s))
      (v,s) in
    let h = repeati (range 0x8)
      (fun i h ->
        let h = h.[i] <- ((h.[i] ^. v.[i]) ^. v.[(i +. 0x8)]) in
        h)
      h in
    h in
  let blake2_internal (data:data_internal_t var) (input_bytes:uint128_t) (kk:key_size_t var) (nn:out_size_t) : Pure vlbytes_t (requires (True)) (ensures ((length res = nn))) =
    let h = copy (_IV var) in
    let h = h.[0x0] <- (((h.[0x0] ^. to_word var 0x1010000) ^. (to_word var kk <<. 0x8)) ^. to_word var nn) in
    let bb = block_bytes var in
    let data_blocks = (length data /. bb) in
    let () = if ((data_blocks > 0x1)) then (let h = repeati (range (data_blocks -. 0x1))
        (fun i h ->
          let h = __F h (to_words_le var slice data (bb *. i) (bb *. (i +. 0x1))) (to_double_word var ((i +. 0x1) *. bb)) False in
          h)
        h in () )else (()) in
    let h = if ((kk = 0x0)) then (let h = __F h (to_words_le var slice data (bb *. (data_blocks -. 0x1)) (bb *. data_blocks)) (to_double_word var input_bytes) True in h )else (let h = __F h (to_words_le var slice data (bb *. (data_blocks -. 0x1)) (bb *. data_blocks)) (to_double_word var (input_bytes +. bb)) True in h) in
    slice from_words_le var h None nn in
  let blake2 (data:data_t var) (key:key_t var) (nn:out_size_t var) : Pure vlbytes_t (requires (True)) (ensures ((length res = nn))) =
    let ll = length data in
    let kk = length key in
    let bb = block_bytes var in
    let data_blocks = (((ll -. 0x1) /. bb) +. 0x1) in
    let padded_data_length = (data_blocks *. bb) in
    let padded_data = if ((kk = 0x0)) then (let padded_data = create padded_data_length (u8 0x0) in
      let padded_data = update_slice padded_data None ll data in padded_data )else (let padded_data = create (padded_data_length +. bb) (u8 0x0) in
      let padded_data = update_slice padded_data 0x0 kk key in
      let padded_data = update_slice padded_data bb (bb +. ll) key in padded_data) in
    blake2_internal padded_data ll kk nn in
  blake2
let blake2s = blake2 (variant 0x1)
let blake2b = blake2 (variant 0x0)
*)
