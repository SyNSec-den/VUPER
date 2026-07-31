
type __ = Obj.t

type empty_set = |

val negb : bool -> bool

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> int

type comparison =
| Eq
| Lt
| Gt

val id : __ -> __

type 'a sig0 =
| Exist of 'a

type ('a, 'p) sigT =
| ExistT of 'a * 'p

type char_list = char list  

val pow : int -> int -> int



module Nat :
 sig
  val pred : int -> int

  val add : int -> int -> int

  val double : int -> int

  val mul : int -> int -> int

  val max : int -> int -> int

  val even : int -> bool

  val odd : int -> bool

  val div2 : int -> int

  val shiftl : int -> int -> int

  val bitwise : (bool -> bool -> bool) -> int -> int -> int -> int

  val lnot : int -> int -> int
 end

module Pos :
 sig
  val succ : int -> int

  val add : int -> int -> int

  val add_carry : int -> int -> int

  val pred_double : int -> int

  val mul : int -> int -> int

  val iter : ('a1 -> 'a1) -> 'a1 -> int -> 'a1

  val compare_cont : comparison -> int -> int -> comparison

  val compare : int -> int -> comparison

  val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1

  val to_nat : int -> int

  val of_succ_nat : int -> int

  val eq_dec : int -> int -> bool
 end

module N :
 sig
  val add : int -> int -> int

  val mul : int -> int -> int

  val to_nat : int -> int

  val of_nat : int -> int
 end

module Z :
 sig
  val double : int -> int

  val succ_double : int -> int

  val pred_double : int -> int

  val pos_sub : int -> int -> int

  val add : int -> int -> int

  val opp : int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val pow_pos : int -> int -> int

  val pow : int -> int -> int

  val compare : int -> int -> comparison

  val ltb : int -> int -> bool
 end

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val firstn : int -> 'a1 list -> 'a1 list

val skipn : int -> 'a1 list -> 'a1 list

val le_gt_dec : int -> int -> bool

val le_dec : int -> int -> bool



val z_le_dec : int -> int -> bool

val option_bind : 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option

val byte_get_nat : BigArrayExtr.byte_buf -> int -> int option

type byteIdx =
| I0
| I1
| I2
| I3
| I4
| I5
| I6
| I7

val byteIdx_to_nat : byteIdx -> int

val nat_to_ByteIdx : int -> byteIdx

type bytePos = { byte_pos : int; byte_off : byteIdx }

module BA :
 sig
  type coq_Buffer = BigArrayExtr.byte_buf

  val len : coq_Buffer -> int

  type coq_Pos = bytePos

  val to_nat : coq_Pos -> int

  val of_nat : int -> coq_Pos
 end

type flg =
| SameVer
| DiffVer

val flg_add : flg -> flg -> flg

val add_opt : int option -> int option -> int option

type 'a dec_P = 'a -> bool

val sumbool_and1 : bool -> bool -> bool

type 'a serialize =
  BA.coq_Buffer -> BA.coq_Pos -> 'a -> ((BA.coq_Buffer * BA.coq_Pos) * __)
  option

type 'a parse =
  BA.coq_Buffer -> BA.coq_Pos -> (('a sig0 * BA.coq_Pos) * flg) option

val get_byte_len : int -> int

type 't t_Format = { t_Serial : 't serialize; t_Parse : 't parse;
                     t_to_len : ('t -> int option) }

val bind_parse : 'a1 parse -> ('a1 -> __ -> flg -> 'a2 parse) -> 'a2 parse

val proj_parse : 'a1 parse -> ('a1 -> 'a2) -> 'a2 parse

val return_parse : 'a1 sig0 -> flg -> 'a1 parse

val restrict_parse : 'a1 dec_P -> 'a1 parse -> 'a1 parse

val restrict_serialize : 'a1 dec_P -> 'a1 serialize -> 'a1 serialize

val proj_serialize :
  'a1 serialize -> ('a2 -> 'a1) -> 'a2 dec_P -> 'a2 serialize

val sigma_serialize :
  'a1 serialize -> ('a1 -> __ -> 'a2 serialize) -> ('a1 * 'a2) serialize

val append_serialize : 'a1 serialize -> 'a2 serialize -> ('a1 * 'a2) serialize

val sigma_parse : 'a1 parse -> ('a1 -> __ -> 'a2 parse) -> ('a1 * 'a2) parse

val append_parse : 'a1 parse -> 'a2 parse -> ('a1 * 'a2) parse

val mask0 : int -> int -> int -> int

val mask : int -> int -> int -> int

val put_few_bits : int -> int -> int -> int -> int -> int

val get_few_bits : int -> int -> int -> int -> int

val put_k_bytes :
  int -> int -> BigArrayExtr.byte_buf -> int -> BigArrayExtr.byte_buf option

val read_k_bytes : int -> int -> BigArrayExtr.byte_buf -> int option

val put_n_bits : int -> int serialize

val read_n_bits : int -> int parse

val put_n_nat : int -> int serialize

val read_n_nat : int -> int parse

val n_nat_to_len : int -> int -> int option

val basic_n_bit_format : int -> int t_Format

val proj_format :
  'a2 t_Format -> ('a1 -> 'a2) -> ('a2 -> 'a1) -> 'a1 dec_P -> 'a1 t_Format

val sigma_format :
  'a1 t_Format -> ('a1 -> 'a2 t_Format) -> ('a1 * 'a2) t_Format

val append_format : 'a1 t_Format -> 'a2 t_Format -> ('a1 * 'a2) t_Format

val restrict_format : 'a1 t_Format -> ('a1 -> bool) -> 'a1 t_Format

val put_unit : unit serialize

val read_unit : unit parse

val unit_to_len : unit -> int option

val unit_format : unit t_Format

val put_fixed_item :
  'a1 -> BA.coq_Buffer -> BA.coq_Pos -> ((BA.coq_Buffer * BA.coq_Pos) * __)
  option

val read_fixed_item : 'a1 sig0 -> 'a1 parse

val list_serial : 'a1 serialize -> int -> 'a1 list serialize

val list_parse : 'a1 parse -> int -> 'a1 list parse

val list_to_len : ('a1 -> int option) -> int -> 'a1 list -> int option

val list_format : 'a1 t_Format -> int -> 'a1 list t_Format

val bool_format : bool t_Format

val to_bit_sz : int -> int

val nat_format : int -> int t_Format

val nat_enum_format : int -> int t_Format

val nat_range_format : int -> int -> int t_Format

val small_integer_format : int t_Format

val sumbool_neg : bool -> bool

val sumbool_or1 : bool -> bool -> bool

val choose_norm_ext_format :
  'a1 t_Format -> 'a1 t_Format -> 'a1 dec_P -> 'a1 dec_P -> (bool * 'a1)
  t_Format

val normal_ext_format_dec : 'a1 dec_P -> 'a1 dec_P -> 'a1 dec_P

val normal_ext_format :
  'a1 t_Format -> 'a1 t_Format -> 'a1 dec_P -> 'a1 dec_P -> 'a1 t_Format

val choose_len_det_helper3 : bool -> int -> bool

val choose_len_det_format : bool -> int t_Format

val bit_len_format : (bool * int) t_Format

val uncons_len_det_format : int t_Format

val choose_norm_small_det : bool -> int t_Format

val bit_norm_small_len_format : (bool * int) t_Format

val normally_small_len_det_format : int t_Format

val small_enc : int serialize

val small_dec : int parse

val len_det_ranged_ext : int -> int -> int t_Format

val z_range_dec : int -> int -> int -> bool

val ranged_int_format : int -> int -> int t_Format

val sz_to_num_octets : int -> int

val to_2_complement : int -> int -> int

type nat_T = int sig0

val compare_lt_le_dec : int -> int -> int -> bool

val z_to_nat_bin : int -> nat_T * int

val nat_bin_to_z : (nat_T * int) -> int

val int_len_det : int t_Format

val int_len_det_sig : nat_T t_Format

val restrict_nat_pair_dec : int -> int -> bool

val restrict_nat_pair : int -> int t_Format

val nat_pair_format : (nat_T * int) t_Format

val int_format : int t_Format

val int_format_ranged_ext : int -> int -> int t_Format

val of_nat_non_opt : int -> char

val byte_format : char t_Format

val byte_list_format : int -> char list t_Format

type octet_string = char list

val octet_string_no_cons_format : char list t_Format

val octet_string_ranged_format : int -> int -> char list t_Format

val list_bool_format : int -> bool list t_Format

val bool_list_serialize : int -> bool list serialize

val bool_list_parse : int -> bool list parse

type bit_string = int * (char list * int)

type bit_string_fixed = int * (char list * int)

val get_list_len : int -> int

val get_tail_len : int -> int

val bit_string_len_prop_dec : int -> (char list * int) -> bool

val bit_string_format : int -> (char list * int) t_Format

val ranged_nat_format : int -> int -> int t_Format

val bit_string_ranged_format : int -> int -> (int * (char list * int)) t_Format

val fixed_nat_format : int -> int t_Format

val bit_string_fixed_format : int -> (int * (char list * int)) t_Format

val bool_enc : bool serialize

val opt_bind : 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option

val fail_parse : 'a1 parse

val opt_serialize : 'a1 serialize -> 'a1 option serialize

val opt_parse : 'a1 parse -> bool -> 'a1 option parse

val put_fixed_item0 :
  'a1 -> BA.coq_Buffer -> BA.coq_Pos -> ((BA.coq_Buffer * BA.coq_Pos) * __)
  option

val dft_serialize :
  'a1 serialize -> ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 serialize

val dft_parse : 'a1 parse -> 'a1 -> ('a1 -> 'a1 -> bool) -> bool -> 'a1 parse

val append_parse0 : 'a1 parse -> 'a2 parse -> ('a1 * 'a2) parse

val prepend_serialize :
  ('a2 -> 'a1) -> 'a1 serialize -> 'a2 serialize -> 'a2 serialize

val prepend_serialize_fixed :
  'a1 -> 'a1 serialize -> 'a2 serialize -> 'a2 serialize

val length2 : 'a1 list -> int

val proj2_serialize :
  'a2 serialize -> ('a2 -> 'a1) -> ('a1 -> 'a2) -> 'a1 serialize

val proj2_format : 'a2 t_Format -> ('a1 -> 'a2) -> ('a2 -> 'a1) -> 'a1 t_Format

val seq_of_format : 'a1 t_Format -> int -> int -> 'a1 list t_Format

val length_value_format : 'a1 t_Format -> int t_Format -> 'a1 list t_Format

val seq_of_fixed_format : 'a1 t_Format -> int -> 'a1 list t_Format

val seq_of_ext_format : 'a1 t_Format -> int -> int -> 'a1 list t_Format

val num_to_ascii : int -> char

val ascii_to_num : char -> int

val numeric_string_dec : char dec_P

val numeric_string__Format : char t_Format

val ia5_string__Format : char t_Format

val utf8_string__Format : string t_Format

type ('x, 'f) list_to_prod = __

type typ =
| Typ_cons

type typ_set = __

type ('x, 'f) list_to_prod_set = __

type get_formats = (typ, typ_set t_Format) list_to_prod

type get_serial_prod = (typ, typ_set serialize) list_to_prod

type get_parse_prod = (typ, typ_set parse) list_to_prod

type get_to_len_prod = (typ, typ_set -> int option) list_to_prod

val fmt_to_prod :
  typ list -> get_formats -> (__ -> __ -> __ t_Format -> 'a1) -> 'a1 -> (typ,
  'a1) list_to_prod

val fmt_to_prod_no_cond :
  typ list -> get_formats -> (__ -> __ -> __ t_Format -> 'a1) -> 'a1 -> (typ,
  'a1) list_to_prod

type choice = (int, typ_set) sigT

val put_empty : empty_set serialize

val read_empty : empty_set parse

val empty_to_len : empty_set -> int option

val empty_format : empty_set t_Format

val get_remaining_bits : int -> int

val det_enc : int serialize

val det_dec : int parse

val open_typ_serialize : 'a1 serialize -> ('a1 -> int option) -> 'a1 serialize

val skip_some_bits : int -> int parse

val open_typ_parse : 'a1 parse -> 'a1 parse

val skip_1_byte : unit parse

val skip_n_bytes : int -> unit parse

val open_type_skip_parse : unit parse

val open_type_to_len : ('a1 -> int option) -> 'a1 -> int option

type seq_elem =
| Nor
| Opt
| Dft of __ * (__ -> __ -> bool)

type seq_elem_to_type = __

type seq_type = (seq_elem, seq_elem_to_type) list_to_prod_set

val bit_list_len : seq_elem list -> int

val seq_type_to_bit_list : seq_elem list -> seq_type -> bool list

type seq_elem_to_set = __

type seq_elem_to_serial = seq_elem_to_set serialize

type seq_elem_to_parse = seq_elem_to_set parse

type seq_elem_to_format = seq_elem_to_set t_Format

type seq_format_prod = (seq_elem, seq_elem_to_format) list_to_prod

type seq_serial_prod = (seq_elem, seq_elem_to_serial) list_to_prod

type seq_to_len_prod = (seq_elem, seq_elem_to_set -> int option) list_to_prod

val seq_serialize_latter :
  seq_elem list -> seq_serial_prod -> seq_type serialize

val seq_serialize : seq_elem list -> seq_serial_prod -> seq_type serialize

type seq_parse_prod = (seq_elem, seq_elem_to_parse) list_to_prod

val seq_parse_latter :
  seq_elem list -> seq_parse_prod -> bool list -> seq_type parse

val seq_parse : seq_elem list -> seq_parse_prod -> seq_type parse

val seq_to_len_latter :
  seq_elem list -> seq_to_len_prod -> seq_type -> int option

val seq_to_len : seq_elem list -> seq_to_len_prod -> seq_type -> int option

type ext_elem_to_type = typ_set option

type ('x, 'f, 'default) list_to_prod_dft = __

type seq_ext_type = (typ, ext_elem_to_type, unit) list_to_prod_dft

val ext_serialize_latter :
  typ list -> get_serial_prod -> get_to_len_prod -> seq_ext_type serialize

val check_all_none_bool : typ list -> seq_ext_type -> bool

val check_all_none_dec : typ list -> seq_ext_type dec_P

val opt_bool : 'a1 option -> bool

val ext_to_bit_list : typ list -> seq_ext_type -> bool list

val ext_serialize :
  typ list -> get_serial_prod -> get_to_len_prod -> seq_ext_type serialize

val to_parse_latter_eq :
  typ list -> get_parse_prod -> bool list -> seq_ext_type parse

val ext_all_none : typ list -> seq_ext_type

val to_parse_none : typ list -> seq_ext_type parse

val to_parse_latter_le :
  typ list -> get_parse_prod -> bool list -> seq_ext_type parse

val to_parse_skip : int -> bool list -> unit parse

val to_parse_latter_ge :
  typ list -> get_parse_prod -> bool list -> seq_ext_type parse

type three_split =
| Left3
| Middle3
| Right3

val lt_le_eq_dec : int -> int -> bool

val lt_eq_lt_dec_new : int -> int -> three_split

val ext_parse : typ list -> get_parse_prod -> seq_ext_type parse

val seq_ext_to_len_latter :
  typ list -> get_to_len_prod -> seq_ext_type -> int option

val seq_ext_to_len : typ list -> get_to_len_prod -> seq_ext_type -> int option

val seq_ext_serialize :
  seq_elem list -> seq_serial_prod -> typ list -> get_serial_prod ->
  get_to_len_prod -> (seq_type * seq_ext_type) serialize

val seq_ext_parse :
  seq_elem list -> seq_parse_prod -> typ list -> get_parse_prod ->
  (seq_type * seq_ext_type) parse

val seq_ext_to_len0 :
  seq_elem list -> seq_to_len_prod -> typ list -> get_to_len_prod ->
  (seq_type * seq_ext_type) -> int option

val fmt_to_seq_prod :
  seq_elem list -> seq_format_prod -> (__ -> __ -> __ t_Format -> 'a1) -> 'a1
  -> (seq_elem, 'a1) list_to_prod

val fmt_to_seq_prod_no_cond :
  seq_elem list -> seq_format_prod -> (__ -> __ -> __ t_Format -> 'a1) -> 'a1
  -> (seq_elem, 'a1) list_to_prod

val seq_format : seq_elem list -> seq_format_prod -> seq_type t_Format

val seq_ext_format :
  seq_elem list -> seq_format_prod -> typ list -> get_formats ->
  (seq_type * seq_ext_type) t_Format

val proj3_format : 'a2 t_Format -> ('a1 -> 'a2) -> ('a2 -> 'a1) -> 'a1 t_Format

val unit__Format : unit t_Format

val bool__Format : bool t_Format

val sum_serial : 'a1 serialize -> 'a2 serialize -> ('a1, 'a2) sum serialize

val sum_parse : 'a1 parse -> 'a2 parse -> ('a1, 'a2) sum parse

val sum_to_len :
  ('a1 -> int option) -> ('a2 -> int option) -> ('a1, 'a2) sum -> int option

val sum_format : 'a1 t_Format -> 'a2 t_Format -> ('a1, 'a2) sum t_Format

type stationID__Type = int

val stationID__Format : int t_Format

type itsPduHeader__Type = { itsPduHeader__protocolVersion : int;
                            itsPduHeader__messageID : int;
                            itsPduHeader__stationID : stationID__Type }

val itsPduHeader__list : seq_elem list

val itsPduHeader__protocolVersion__Format : int t_Format

val itsPduHeader__messageID__Format : int t_Format

type itsPduHeader__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val itsPduHeader__Format_list : itsPduHeader__Format_Type

val itsPduHeader__list__Format : seq_type t_Format

val itsPduHeader__F1 :
  itsPduHeader__Type -> int * (int * (stationID__Type * unit))

val itsPduHeader__F2 : seq_type -> itsPduHeader__Type

val itsPduHeader__Format : itsPduHeader__Type t_Format

type generationDeltaTime__Type = int

val generationDeltaTime__Format : int t_Format

type stationType__Type = int

val stationType__Format : int t_Format

type latitude__Type = int

val latitude__Format : int t_Format

type longitude__Type = int

val longitude__Format : int t_Format

type semiAxisLength__Type = int

val semiAxisLength__Format : int t_Format

type headingValue__Type = int

val headingValue__Format : int t_Format

type posConfidenceEllipse__Type = { posConfidenceEllipse__semiMajorConfidence : 
                                    semiAxisLength__Type;
                                    posConfidenceEllipse__semiMinorConfidence : 
                                    semiAxisLength__Type;
                                    posConfidenceEllipse__semiMajorOrientation : 
                                    headingValue__Type }

val posConfidenceEllipse__list : seq_elem list

type posConfidenceEllipse__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val posConfidenceEllipse__Format_list : posConfidenceEllipse__Format_Type

val posConfidenceEllipse__list__Format : seq_type t_Format

val posConfidenceEllipse__F1 :
  posConfidenceEllipse__Type ->
  semiAxisLength__Type * (semiAxisLength__Type * (headingValue__Type * unit))

val posConfidenceEllipse__F2 : seq_type -> posConfidenceEllipse__Type

val posConfidenceEllipse__Format : posConfidenceEllipse__Type t_Format

type altitudeValue__Type = int

val altitudeValue__Format : int t_Format

type altitudeConfidence__Type =
| AltitudeConfidence__alt_000_01
| AltitudeConfidence__alt_000_02
| AltitudeConfidence__alt_000_05
| AltitudeConfidence__alt_000_10
| AltitudeConfidence__alt_000_20
| AltitudeConfidence__alt_000_50
| AltitudeConfidence__alt_001_00
| AltitudeConfidence__alt_002_00
| AltitudeConfidence__alt_005_00
| AltitudeConfidence__alt_010_00
| AltitudeConfidence__alt_020_00
| AltitudeConfidence__alt_050_00
| AltitudeConfidence__alt_100_00
| AltitudeConfidence__alt_200_00
| AltitudeConfidence__outOfRange
| AltitudeConfidence__unavailable

val altitudeConfidence__nat__Format : int t_Format

val altitudeConfidence__F1 : altitudeConfidence__Type -> int

val altitudeConfidence__F2 : int -> altitudeConfidence__Type

val altitudeConfidence__Format : altitudeConfidence__Type t_Format

type altitude__Type = { altitude__altitudeValue : altitudeValue__Type;
                        altitude__altitudeConfidence : altitudeConfidence__Type }

val altitude__list : seq_elem list

type altitude__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val altitude__Format_list : altitude__Format_Type

val altitude__list__Format : seq_type t_Format

val altitude__F1 :
  altitude__Type -> altitudeValue__Type * (altitudeConfidence__Type * unit)

val altitude__F2 : seq_type -> altitude__Type

val altitude__Format : altitude__Type t_Format

type referencePosition__Type = { referencePosition__latitude : latitude__Type;
                                 referencePosition__longitude : longitude__Type;
                                 referencePosition__positionConfidenceEllipse : 
                                 posConfidenceEllipse__Type;
                                 referencePosition__altitude : altitude__Type }

val referencePosition__list : seq_elem list

type referencePosition__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

val referencePosition__Format_list : referencePosition__Format_Type

val referencePosition__list__Format : seq_type t_Format

val referencePosition__F1 :
  referencePosition__Type ->
  latitude__Type * (longitude__Type * (posConfidenceEllipse__Type * (altitude__Type * unit)))

val referencePosition__F2 : seq_type -> referencePosition__Type

val referencePosition__Format : referencePosition__Type t_Format

type basicContainer__Type = { basicContainer__stationType : stationType__Type;
                              basicContainer__referencePosition : referencePosition__Type }

val basicContainer__root_list : seq_elem list

val basicContainer__ext_list : typ list

type basicContainer__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val basicContainer__root_Format_list : basicContainer__root_Format_Type

type basicContainer__ext_Format_Type = unit t_Format

val basicContainer__ext_Format_list : basicContainer__ext_Format_Type

type basicContainer__list_type = seq_type * seq_ext_type

val basicContainer__list_format : basicContainer__list_type t_Format

val basicContainer__F1 : basicContainer__Type -> basicContainer__list_type

val basicContainer__F2 : basicContainer__list_type -> basicContainer__Type

val basicContainer__Format : basicContainer__Type t_Format

type headingConfidence__Type = int

val headingConfidence__Format : int t_Format

type heading__Type = { heading__headingValue : headingValue__Type;
                       heading__headingConfidence : headingConfidence__Type }

val heading__list : seq_elem list

type heading__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val heading__Format_list : heading__Format_Type

val heading__list__Format : seq_type t_Format

val heading__F1 :
  heading__Type -> headingValue__Type * (headingConfidence__Type * unit)

val heading__F2 : seq_type -> heading__Type

val heading__Format : heading__Type t_Format

type speedValue__Type = int

val speedValue__Format : int t_Format

type speedConfidence__Type = int

val speedConfidence__Format : int t_Format

type speed__Type = { speed__speedValue : speedValue__Type;
                     speed__speedConfidence : speedConfidence__Type }

val speed__list : seq_elem list

type speed__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val speed__Format_list : speed__Format_Type

val speed__list__Format : seq_type t_Format

val speed__F1 :
  speed__Type -> speedValue__Type * (speedConfidence__Type * unit)

val speed__F2 : seq_type -> speed__Type

val speed__Format : speed__Type t_Format

type driveDirection__Type =
| DriveDirection__forward
| DriveDirection__backward
| DriveDirection__unavailable

val driveDirection__nat__Format : int t_Format

val driveDirection__F1 : driveDirection__Type -> int

val driveDirection__F2 : int -> driveDirection__Type

val driveDirection__Format : driveDirection__Type t_Format

type vehicleLengthValue__Type = int

val vehicleLengthValue__Format : int t_Format

type vehicleLengthConfidenceIndication__Type =
| VehicleLengthConfidenceIndication__noTrailerPresent
| VehicleLengthConfidenceIndication__trailerPresentWithKnownLength
| VehicleLengthConfidenceIndication__trailerPresentWithUnknownLength
| VehicleLengthConfidenceIndication__trailerPresenceIsUnknown
| VehicleLengthConfidenceIndication__unavailable

val vehicleLengthConfidenceIndication__nat__Format : int t_Format

val vehicleLengthConfidenceIndication__F1 :
  vehicleLengthConfidenceIndication__Type -> int

val vehicleLengthConfidenceIndication__F2 :
  int -> vehicleLengthConfidenceIndication__Type

val vehicleLengthConfidenceIndication__Format :
  vehicleLengthConfidenceIndication__Type t_Format

type vehicleLength__Type = { vehicleLength__vehicleLengthValue : vehicleLengthValue__Type;
                             vehicleLength__vehicleLengthConfidenceIndication : 
                             vehicleLengthConfidenceIndication__Type }

val vehicleLength__list : seq_elem list

type vehicleLength__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val vehicleLength__Format_list : vehicleLength__Format_Type

val vehicleLength__list__Format : seq_type t_Format

val vehicleLength__F1 :
  vehicleLength__Type ->
  vehicleLengthValue__Type * (vehicleLengthConfidenceIndication__Type * unit)

val vehicleLength__F2 : seq_type -> vehicleLength__Type

val vehicleLength__Format : vehicleLength__Type t_Format

type vehicleWidth__Type = int

val vehicleWidth__Format : int t_Format

type longitudinalAccelerationValue__Type = int

val longitudinalAccelerationValue__Format : int t_Format

type accelerationConfidence__Type = int

val accelerationConfidence__Format : int t_Format

type longitudinalAcceleration__Type = { longitudinalAcceleration__longitudinalAccelerationValue : 
                                        longitudinalAccelerationValue__Type;
                                        longitudinalAcceleration__longitudinalAccelerationConfidence : 
                                        accelerationConfidence__Type }

val longitudinalAcceleration__list : seq_elem list

type longitudinalAcceleration__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val longitudinalAcceleration__Format_list :
  longitudinalAcceleration__Format_Type

val longitudinalAcceleration__list__Format : seq_type t_Format

val longitudinalAcceleration__F1 :
  longitudinalAcceleration__Type ->
  longitudinalAccelerationValue__Type * (accelerationConfidence__Type * unit)

val longitudinalAcceleration__F2 : seq_type -> longitudinalAcceleration__Type

val longitudinalAcceleration__Format : longitudinalAcceleration__Type t_Format

type curvatureValue__Type = int

val curvatureValue__Format : int t_Format

type curvatureConfidence__Type =
| CurvatureConfidence__onePerMeter_0_00002
| CurvatureConfidence__onePerMeter_0_0001
| CurvatureConfidence__onePerMeter_0_0005
| CurvatureConfidence__onePerMeter_0_002
| CurvatureConfidence__onePerMeter_0_01
| CurvatureConfidence__onePerMeter_0_1
| CurvatureConfidence__outOfRange
| CurvatureConfidence__unavailable

val curvatureConfidence__nat__Format : int t_Format

val curvatureConfidence__F1 : curvatureConfidence__Type -> int

val curvatureConfidence__F2 : int -> curvatureConfidence__Type

val curvatureConfidence__Format : curvatureConfidence__Type t_Format

type curvature__Type = { curvature__curvatureValue : curvatureValue__Type;
                         curvature__curvatureConfidence : curvatureConfidence__Type }

val curvature__list : seq_elem list

type curvature__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val curvature__Format_list : curvature__Format_Type

val curvature__list__Format : seq_type t_Format

val curvature__F1 :
  curvature__Type -> curvatureValue__Type * (curvatureConfidence__Type * unit)

val curvature__F2 : seq_type -> curvature__Type

val curvature__Format : curvature__Type t_Format

type curvatureCalculationMode__root__Type =
| CurvatureCalculationMode__root__yawRateUsed
| CurvatureCalculationMode__root__yawRateNotUsed
| CurvatureCalculationMode__root__unavailable

val curvatureCalculationMode__root__nat__Format : int t_Format

val curvatureCalculationMode__root__F1 :
  curvatureCalculationMode__root__Type -> int

val curvatureCalculationMode__root__F2 :
  int -> curvatureCalculationMode__root__Type

type curvatureCalculationMode__ext__Type = empty_set

type curvatureCalculationMode__Type =
  (curvatureCalculationMode__root__Type, curvatureCalculationMode__ext__Type)
  sum

val curvatureCalculationMode__root__Format :
  curvatureCalculationMode__root__Type t_Format

val curvatureCalculationMode__ext__Format :
  curvatureCalculationMode__ext__Type t_Format

val curvatureCalculationMode__Format : curvatureCalculationMode__Type t_Format

type yawRateValue__Type = int

val yawRateValue__Format : int t_Format

type yawRateConfidence__Type =
| YawRateConfidence__degSec_000_01
| YawRateConfidence__degSec_000_05
| YawRateConfidence__degSec_000_10
| YawRateConfidence__degSec_001_00
| YawRateConfidence__degSec_005_00
| YawRateConfidence__degSec_010_00
| YawRateConfidence__degSec_100_00
| YawRateConfidence__outOfRange
| YawRateConfidence__unavailable

val yawRateConfidence__nat__Format : int t_Format

val yawRateConfidence__F1 : yawRateConfidence__Type -> int

val yawRateConfidence__F2 : int -> yawRateConfidence__Type

val yawRateConfidence__Format : yawRateConfidence__Type t_Format

type yawRate__Type = { yawRate__yawRateValue : yawRateValue__Type;
                       yawRate__yawRateConfidence : yawRateConfidence__Type }

val yawRate__list : seq_elem list

type yawRate__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val yawRate__Format_list : yawRate__Format_Type

val yawRate__list__Format : seq_type t_Format

val yawRate__F1 :
  yawRate__Type -> yawRateValue__Type * (yawRateConfidence__Type * unit)

val yawRate__F2 : seq_type -> yawRate__Type

val yawRate__Format : yawRate__Type t_Format

type accelerationControl__Type = bit_string_fixed

val accelerationControl__Format : accelerationControl__Type t_Format

type lanePosition__Type = int

val lanePosition__Format : int t_Format

type steeringWheelAngleValue__Type = int

val steeringWheelAngleValue__Format : int t_Format

type steeringWheelAngleConfidence__Type = int

val steeringWheelAngleConfidence__Format : int t_Format

type steeringWheelAngle__Type = { steeringWheelAngle__steeringWheelAngleValue : 
                                  steeringWheelAngleValue__Type;
                                  steeringWheelAngle__steeringWheelAngleConfidence : 
                                  steeringWheelAngleConfidence__Type }

val steeringWheelAngle__list : seq_elem list

type steeringWheelAngle__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val steeringWheelAngle__Format_list : steeringWheelAngle__Format_Type

val steeringWheelAngle__list__Format : seq_type t_Format

val steeringWheelAngle__F1 :
  steeringWheelAngle__Type ->
  steeringWheelAngleValue__Type * (steeringWheelAngleConfidence__Type * unit)

val steeringWheelAngle__F2 : seq_type -> steeringWheelAngle__Type

val steeringWheelAngle__Format : steeringWheelAngle__Type t_Format

type lateralAccelerationValue__Type = int

val lateralAccelerationValue__Format : int t_Format

type lateralAcceleration__Type = { lateralAcceleration__lateralAccelerationValue : 
                                   lateralAccelerationValue__Type;
                                   lateralAcceleration__lateralAccelerationConfidence : 
                                   accelerationConfidence__Type }

val lateralAcceleration__list : seq_elem list

type lateralAcceleration__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val lateralAcceleration__Format_list : lateralAcceleration__Format_Type

val lateralAcceleration__list__Format : seq_type t_Format

val lateralAcceleration__F1 :
  lateralAcceleration__Type ->
  lateralAccelerationValue__Type * (accelerationConfidence__Type * unit)

val lateralAcceleration__F2 : seq_type -> lateralAcceleration__Type

val lateralAcceleration__Format : lateralAcceleration__Type t_Format

type verticalAccelerationValue__Type = int

val verticalAccelerationValue__Format : int t_Format

type verticalAcceleration__Type = { verticalAcceleration__verticalAccelerationValue : 
                                    verticalAccelerationValue__Type;
                                    verticalAcceleration__verticalAccelerationConfidence : 
                                    accelerationConfidence__Type }

val verticalAcceleration__list : seq_elem list

type verticalAcceleration__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val verticalAcceleration__Format_list : verticalAcceleration__Format_Type

val verticalAcceleration__list__Format : seq_type t_Format

val verticalAcceleration__F1 :
  verticalAcceleration__Type ->
  verticalAccelerationValue__Type * (accelerationConfidence__Type * unit)

val verticalAcceleration__F2 : seq_type -> verticalAcceleration__Type

val verticalAcceleration__Format : verticalAcceleration__Type t_Format

type performanceClass__Type = int

val performanceClass__Format : int t_Format

type protectedZoneID__Type = int

val protectedZoneID__Format : int t_Format

type cenDsrcTollingZoneID__Type = protectedZoneID__Type

val cenDsrcTollingZoneID__Format : int t_Format

type cenDsrcTollingZone__Type = { cenDsrcTollingZone__protectedZoneLatitude : 
                                  latitude__Type;
                                  cenDsrcTollingZone__protectedZoneLongitude : 
                                  longitude__Type;
                                  cenDsrcTollingZone__cenDsrcTollingZoneID : 
                                  cenDsrcTollingZoneID__Type option }

val cenDsrcTollingZone__root_list : seq_elem list

val cenDsrcTollingZone__ext_list : typ list

type cenDsrcTollingZone__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val cenDsrcTollingZone__root_Format_list : cenDsrcTollingZone__root_Format_Type

type cenDsrcTollingZone__ext_Format_Type = unit t_Format

val cenDsrcTollingZone__ext_Format_list : cenDsrcTollingZone__ext_Format_Type

type cenDsrcTollingZone__list_type = seq_type * seq_ext_type

val cenDsrcTollingZone__list_format : cenDsrcTollingZone__list_type t_Format

val cenDsrcTollingZone__F1 :
  cenDsrcTollingZone__Type -> cenDsrcTollingZone__list_type

val cenDsrcTollingZone__F2 :
  cenDsrcTollingZone__list_type -> cenDsrcTollingZone__Type

val cenDsrcTollingZone__Format : cenDsrcTollingZone__Type t_Format

type basicVehicleContainerHighFrequency__Type = { basicVehicleContainerHighFrequency__heading : 
                                                  heading__Type;
                                                  basicVehicleContainerHighFrequency__speed : 
                                                  speed__Type;
                                                  basicVehicleContainerHighFrequency__driveDirection : 
                                                  driveDirection__Type;
                                                  basicVehicleContainerHighFrequency__vehicleLength : 
                                                  vehicleLength__Type;
                                                  basicVehicleContainerHighFrequency__vehicleWidth : 
                                                  vehicleWidth__Type;
                                                  basicVehicleContainerHighFrequency__longitudinalAcceleration : 
                                                  longitudinalAcceleration__Type;
                                                  basicVehicleContainerHighFrequency__curvature : 
                                                  curvature__Type;
                                                  basicVehicleContainerHighFrequency__curvatureCalculationMode : 
                                                  curvatureCalculationMode__Type;
                                                  basicVehicleContainerHighFrequency__yawRate : 
                                                  yawRate__Type;
                                                  basicVehicleContainerHighFrequency__accelerationControl : 
                                                  accelerationControl__Type
                                                  option;
                                                  basicVehicleContainerHighFrequency__lanePosition : 
                                                  lanePosition__Type option;
                                                  basicVehicleContainerHighFrequency__steeringWheelAngle : 
                                                  steeringWheelAngle__Type
                                                  option;
                                                  basicVehicleContainerHighFrequency__lateralAcceleration : 
                                                  lateralAcceleration__Type
                                                  option;
                                                  basicVehicleContainerHighFrequency__verticalAcceleration : 
                                                  verticalAcceleration__Type
                                                  option;
                                                  basicVehicleContainerHighFrequency__performanceClass : 
                                                  performanceClass__Type option;
                                                  basicVehicleContainerHighFrequency__cenDsrcTollingZone : 
                                                  cenDsrcTollingZone__Type
                                                  option }

val basicVehicleContainerHighFrequency__list : seq_elem list

type basicVehicleContainerHighFrequency__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))))))))))))))

val basicVehicleContainerHighFrequency__Format_list :
  basicVehicleContainerHighFrequency__Format_Type

val basicVehicleContainerHighFrequency__list__Format : seq_type t_Format

val basicVehicleContainerHighFrequency__F1 :
  basicVehicleContainerHighFrequency__Type ->
  heading__Type * (speed__Type * (driveDirection__Type * (vehicleLength__Type * (vehicleWidth__Type * (longitudinalAcceleration__Type * (curvature__Type * (curvatureCalculationMode__Type * (yawRate__Type * (accelerationControl__Type
  option * (lanePosition__Type option * (steeringWheelAngle__Type
  option * (lateralAcceleration__Type option * (verticalAcceleration__Type
  option * (performanceClass__Type option * (cenDsrcTollingZone__Type
  option * unit)))))))))))))))

val basicVehicleContainerHighFrequency__F2 :
  seq_type -> basicVehicleContainerHighFrequency__Type

val basicVehicleContainerHighFrequency__Format :
  basicVehicleContainerHighFrequency__Type t_Format

type protectedZoneType__root__Type =
| ProtectedZoneType__root__permanentCenDsrcTolling

val protectedZoneType__root__nat__Format : int t_Format

val protectedZoneType__root__F1 : protectedZoneType__root__Type -> int

val protectedZoneType__root__F2 : int -> protectedZoneType__root__Type

type protectedZoneType__ext__Type =
| ProtectedZoneType__ext__temporaryCenDsrcTolling

val protectedZoneType__ext__F1 : protectedZoneType__ext__Type -> int

val protectedZoneType__ext__F2 : int -> protectedZoneType__ext__Type

val protectedZoneType__ext__helper_format : int t_Format

type protectedZoneType__Type =
  (protectedZoneType__root__Type, protectedZoneType__ext__Type) sum

val protectedZoneType__root__Format : protectedZoneType__root__Type t_Format

val protectedZoneType__ext__Format : protectedZoneType__ext__Type t_Format

val protectedZoneType__Format : protectedZoneType__Type t_Format

type timestampIts__Type = int

val timestampIts__Format : int t_Format

type protectedZoneRadius__Type = int

val protectedZoneRadius__Format : int t_Format

type protectedCommunicationZone__Type = { protectedCommunicationZone__protectedZoneType : 
                                          protectedZoneType__Type;
                                          protectedCommunicationZone__expiryTime : 
                                          timestampIts__Type option;
                                          protectedCommunicationZone__protectedZoneLatitude : 
                                          latitude__Type;
                                          protectedCommunicationZone__protectedZoneLongitude : 
                                          longitude__Type;
                                          protectedCommunicationZone__protectedZoneRadius : 
                                          protectedZoneRadius__Type option;
                                          protectedCommunicationZone__protectedZoneID : 
                                          protectedZoneID__Type option }

val protectedCommunicationZone__root_list : seq_elem list

val protectedCommunicationZone__ext_list : typ list

type protectedCommunicationZone__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))))

val protectedCommunicationZone__root_Format_list :
  protectedCommunicationZone__root_Format_Type

type protectedCommunicationZone__ext_Format_Type = unit t_Format

val protectedCommunicationZone__ext_Format_list :
  protectedCommunicationZone__ext_Format_Type

type protectedCommunicationZone__list_type = seq_type * seq_ext_type

val protectedCommunicationZone__list_format :
  protectedCommunicationZone__list_type t_Format

val protectedCommunicationZone__F1 :
  protectedCommunicationZone__Type -> protectedCommunicationZone__list_type

val protectedCommunicationZone__F2 :
  protectedCommunicationZone__list_type -> protectedCommunicationZone__Type

val protectedCommunicationZone__Format :
  protectedCommunicationZone__Type t_Format

type protectedCommunicationZonesRSU__Type =
  protectedCommunicationZone__Type list

val protectedCommunicationZonesRSU__Format :
  protectedCommunicationZonesRSU__Type t_Format

type rSUContainerHighFrequency__Type = { rSUContainerHighFrequency__protectedCommunicationZonesRSU : 
                                         protectedCommunicationZonesRSU__Type
                                         option }

val rSUContainerHighFrequency__root_list : seq_elem list

val rSUContainerHighFrequency__ext_list : typ list

type rSUContainerHighFrequency__root_Format_Type =
  seq_elem_to_format * seq_elem_to_format

val rSUContainerHighFrequency__root_Format_list :
  rSUContainerHighFrequency__root_Format_Type

type rSUContainerHighFrequency__ext_Format_Type = unit t_Format

val rSUContainerHighFrequency__ext_Format_list :
  rSUContainerHighFrequency__ext_Format_Type

type rSUContainerHighFrequency__list_type = seq_type * seq_ext_type

val rSUContainerHighFrequency__list_format :
  rSUContainerHighFrequency__list_type t_Format

val rSUContainerHighFrequency__F1 :
  rSUContainerHighFrequency__Type -> rSUContainerHighFrequency__list_type

val rSUContainerHighFrequency__F2 :
  rSUContainerHighFrequency__list_type -> rSUContainerHighFrequency__Type

val rSUContainerHighFrequency__Format :
  rSUContainerHighFrequency__Type t_Format

type highFrequencyContainer__root__Type =
| HighFrequencyContainer__root__basicVehicleContainerHighFrequency of 
   basicVehicleContainerHighFrequency__Type
| HighFrequencyContainer__root__rsuContainerHighFrequency of rSUContainerHighFrequency__Type

type highFrequencyContainer__ext__Type = empty_set

type highFrequencyContainer__Type =
  (highFrequencyContainer__root__Type, highFrequencyContainer__ext__Type) sum

val highFrequencyContainer__root__list__Format : (int, __) sigT t_Format

val highFrequencyContainer__root__F1 :
  highFrequencyContainer__root__Type -> choice

val highFrequencyContainer__root__F2 :
  choice -> highFrequencyContainer__root__Type

val highFrequencyContainer__root__Format :
  highFrequencyContainer__root__Type t_Format

val highFrequencyContainer__ext__Format :
  highFrequencyContainer__ext__Type t_Format

val highFrequencyContainer__Format : highFrequencyContainer__Type t_Format

type vehicleRole__Type =
| VehicleRole__default
| VehicleRole__publicTransport
| VehicleRole__specialTransport
| VehicleRole__dangerousGoods
| VehicleRole__roadWork
| VehicleRole__rescue
| VehicleRole__emergency
| VehicleRole__safetyCar
| VehicleRole__agriculture
| VehicleRole__commercial
| VehicleRole__military
| VehicleRole__roadOperator
| VehicleRole__taxi
| VehicleRole__reserved1
| VehicleRole__reserved2
| VehicleRole__reserved3

val vehicleRole__nat__Format : int t_Format

val vehicleRole__F1 : vehicleRole__Type -> int

val vehicleRole__F2 : int -> vehicleRole__Type

val vehicleRole__Format : vehicleRole__Type t_Format

type exteriorLights__Type = bit_string_fixed

val exteriorLights__Format : exteriorLights__Type t_Format

type deltaLatitude__Type = int

val deltaLatitude__Format : int t_Format

type deltaLongitude__Type = int

val deltaLongitude__Format : int t_Format

type deltaAltitude__Type = int

val deltaAltitude__Format : int t_Format

type deltaReferencePosition__Type = { deltaReferencePosition__deltaLatitude : 
                                      deltaLatitude__Type;
                                      deltaReferencePosition__deltaLongitude : 
                                      deltaLongitude__Type;
                                      deltaReferencePosition__deltaAltitude : 
                                      deltaAltitude__Type }

val deltaReferencePosition__list : seq_elem list

type deltaReferencePosition__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val deltaReferencePosition__Format_list : deltaReferencePosition__Format_Type

val deltaReferencePosition__list__Format : seq_type t_Format

val deltaReferencePosition__F1 :
  deltaReferencePosition__Type ->
  deltaLatitude__Type * (deltaLongitude__Type * (deltaAltitude__Type * unit))

val deltaReferencePosition__F2 : seq_type -> deltaReferencePosition__Type

val deltaReferencePosition__Format : deltaReferencePosition__Type t_Format

type pathDeltaTime__Type = int

val pathDeltaTime__Format : int t_Format

type pathPoint__Type = { pathPoint__pathPosition : deltaReferencePosition__Type;
                         pathPoint__pathDeltaTime : pathDeltaTime__Type option }

val pathPoint__list : seq_elem list

type pathPoint__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val pathPoint__Format_list : pathPoint__Format_Type

val pathPoint__list__Format : seq_type t_Format

val pathPoint__F1 :
  pathPoint__Type -> deltaReferencePosition__Type * (pathDeltaTime__Type
  option * unit)

val pathPoint__F2 : seq_type -> pathPoint__Type

val pathPoint__Format : pathPoint__Type t_Format

type pathHistory__Type = pathPoint__Type list

val pathHistory__Format : pathHistory__Type t_Format

type basicVehicleContainerLowFrequency__Type = { basicVehicleContainerLowFrequency__vehicleRole : 
                                                 vehicleRole__Type;
                                                 basicVehicleContainerLowFrequency__exteriorLights : 
                                                 exteriorLights__Type;
                                                 basicVehicleContainerLowFrequency__pathHistory : 
                                                 pathHistory__Type }

val basicVehicleContainerLowFrequency__list : seq_elem list

type basicVehicleContainerLowFrequency__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val basicVehicleContainerLowFrequency__Format_list :
  basicVehicleContainerLowFrequency__Format_Type

val basicVehicleContainerLowFrequency__list__Format : seq_type t_Format

val basicVehicleContainerLowFrequency__F1 :
  basicVehicleContainerLowFrequency__Type ->
  vehicleRole__Type * (exteriorLights__Type * (pathHistory__Type * unit))

val basicVehicleContainerLowFrequency__F2 :
  seq_type -> basicVehicleContainerLowFrequency__Type

val basicVehicleContainerLowFrequency__Format :
  basicVehicleContainerLowFrequency__Type t_Format

type lowFrequencyContainer__root__Type =
| LowFrequencyContainer__root__basicVehicleContainerLowFrequency of basicVehicleContainerLowFrequency__Type

type lowFrequencyContainer__ext__Type = empty_set

type lowFrequencyContainer__Type =
  (lowFrequencyContainer__root__Type, lowFrequencyContainer__ext__Type) sum

val lowFrequencyContainer__root__F1 :
  lowFrequencyContainer__root__Type -> basicVehicleContainerLowFrequency__Type

val lowFrequencyContainer__root__F2 :
  basicVehicleContainerLowFrequency__Type -> lowFrequencyContainer__root__Type

val lowFrequencyContainer__root__Format :
  lowFrequencyContainer__root__Type t_Format

val lowFrequencyContainer__ext__Format :
  lowFrequencyContainer__ext__Type t_Format

val lowFrequencyContainer__Format : lowFrequencyContainer__Type t_Format

type embarkationStatus__Type = bool

val embarkationStatus__Format : bool t_Format

type ptActivationType__Type = int

val ptActivationType__Format : int t_Format

type ptActivationData__Type = octet_string

val ptActivationData__Format : ptActivationData__Type t_Format

type ptActivation__Type = { ptActivation__ptActivationType : ptActivationType__Type;
                            ptActivation__ptActivationData : ptActivationData__Type }

val ptActivation__list : seq_elem list

type ptActivation__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val ptActivation__Format_list : ptActivation__Format_Type

val ptActivation__list__Format : seq_type t_Format

val ptActivation__F1 :
  ptActivation__Type ->
  ptActivationType__Type * (ptActivationData__Type * unit)

val ptActivation__F2 : seq_type -> ptActivation__Type

val ptActivation__Format : ptActivation__Type t_Format

type publicTransportContainer__Type = { publicTransportContainer__embarkationStatus : 
                                        embarkationStatus__Type;
                                        publicTransportContainer__ptActivation : 
                                        ptActivation__Type option }

val publicTransportContainer__list : seq_elem list

type publicTransportContainer__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val publicTransportContainer__Format_list :
  publicTransportContainer__Format_Type

val publicTransportContainer__list__Format : seq_type t_Format

val publicTransportContainer__F1 :
  publicTransportContainer__Type ->
  embarkationStatus__Type * (ptActivation__Type option * unit)

val publicTransportContainer__F2 : seq_type -> publicTransportContainer__Type

val publicTransportContainer__Format : publicTransportContainer__Type t_Format

type specialTransportType__Type = bit_string_fixed

val specialTransportType__Format : specialTransportType__Type t_Format

type lightBarSirenInUse__Type = bit_string_fixed

val lightBarSirenInUse__Format : lightBarSirenInUse__Type t_Format

type specialTransportContainer__Type = { specialTransportContainer__specialTransportType : 
                                         specialTransportType__Type;
                                         specialTransportContainer__lightBarSirenInUse : 
                                         lightBarSirenInUse__Type }

val specialTransportContainer__list : seq_elem list

type specialTransportContainer__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val specialTransportContainer__Format_list :
  specialTransportContainer__Format_Type

val specialTransportContainer__list__Format : seq_type t_Format

val specialTransportContainer__F1 :
  specialTransportContainer__Type ->
  specialTransportType__Type * (lightBarSirenInUse__Type * unit)

val specialTransportContainer__F2 : seq_type -> specialTransportContainer__Type

val specialTransportContainer__Format :
  specialTransportContainer__Type t_Format

type dangerousGoodsBasic__Type =
| DangerousGoodsBasic__explosives1
| DangerousGoodsBasic__explosives2
| DangerousGoodsBasic__explosives3
| DangerousGoodsBasic__explosives4
| DangerousGoodsBasic__explosives5
| DangerousGoodsBasic__explosives6
| DangerousGoodsBasic__flammableGases
| DangerousGoodsBasic__nonFlammableGases
| DangerousGoodsBasic__toxicGases
| DangerousGoodsBasic__flammableLiquids
| DangerousGoodsBasic__flammableSolids
| DangerousGoodsBasic__substancesLiableToSpontaneousCombustion
| DangerousGoodsBasic__substancesEmittingFlammableGasesUponContactWithWater
| DangerousGoodsBasic__oxidizingSubstances
| DangerousGoodsBasic__organicPeroxides
| DangerousGoodsBasic__toxicSubstances
| DangerousGoodsBasic__infectiousSubstances
| DangerousGoodsBasic__radioactiveMaterial
| DangerousGoodsBasic__corrosiveSubstances
| DangerousGoodsBasic__miscellaneousDangerousSubstances

val dangerousGoodsBasic__nat__Format : int t_Format

val dangerousGoodsBasic__F1 : dangerousGoodsBasic__Type -> int

val dangerousGoodsBasic__F2 : int -> dangerousGoodsBasic__Type

val dangerousGoodsBasic__Format : dangerousGoodsBasic__Type t_Format

type dangerousGoodsContainer__Type = { dangerousGoodsContainer__dangerousGoodsBasic : 
                                       dangerousGoodsBasic__Type }

val dangerousGoodsContainer__list : seq_elem list

type dangerousGoodsContainer__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val dangerousGoodsContainer__Format_list : dangerousGoodsContainer__Format_Type

val dangerousGoodsContainer__list__Format : seq_type t_Format

val dangerousGoodsContainer__F1 :
  dangerousGoodsContainer__Type -> dangerousGoodsBasic__Type * unit

val dangerousGoodsContainer__F2 : seq_type -> dangerousGoodsContainer__Type

val dangerousGoodsContainer__Format : dangerousGoodsContainer__Type t_Format

type roadworksSubCauseCode__Type = int

val roadworksSubCauseCode__Format : int t_Format

type hardShoulderStatus__Type =
| HardShoulderStatus__availableForStopping
| HardShoulderStatus__closed
| HardShoulderStatus__availableForDriving

val hardShoulderStatus__nat__Format : int t_Format

val hardShoulderStatus__F1 : hardShoulderStatus__Type -> int

val hardShoulderStatus__F2 : int -> hardShoulderStatus__Type

val hardShoulderStatus__Format : hardShoulderStatus__Type t_Format

type drivingLaneStatus__Type = bit_string

val drivingLaneStatus__Format : drivingLaneStatus__Type t_Format

type closedLanes__Type = { closedLanes__innerhardShoulderStatus : hardShoulderStatus__Type
                                                                  option;
                           closedLanes__outerhardShoulderStatus : hardShoulderStatus__Type
                                                                  option;
                           closedLanes__drivingLaneStatus : drivingLaneStatus__Type
                                                            option }

val closedLanes__root_list : seq_elem list

val closedLanes__ext_list : typ list

type closedLanes__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val closedLanes__root_Format_list : closedLanes__root_Format_Type

type closedLanes__ext_Format_Type = unit t_Format

val closedLanes__ext_Format_list : closedLanes__ext_Format_Type

type closedLanes__list_type = seq_type * seq_ext_type

val closedLanes__list_format : closedLanes__list_type t_Format

val closedLanes__F1 : closedLanes__Type -> closedLanes__list_type

val closedLanes__F2 : closedLanes__list_type -> closedLanes__Type

val closedLanes__Format : closedLanes__Type t_Format

type roadWorksContainerBasic__Type = { roadWorksContainerBasic__roadworksSubCauseCode : 
                                       roadworksSubCauseCode__Type option;
                                       roadWorksContainerBasic__lightBarSirenInUse : 
                                       lightBarSirenInUse__Type;
                                       roadWorksContainerBasic__closedLanes : 
                                       closedLanes__Type option }

val roadWorksContainerBasic__list : seq_elem list

type roadWorksContainerBasic__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val roadWorksContainerBasic__Format_list : roadWorksContainerBasic__Format_Type

val roadWorksContainerBasic__list__Format : seq_type t_Format

val roadWorksContainerBasic__F1 :
  roadWorksContainerBasic__Type -> roadworksSubCauseCode__Type
  option * (lightBarSirenInUse__Type * (closedLanes__Type option * unit))

val roadWorksContainerBasic__F2 : seq_type -> roadWorksContainerBasic__Type

val roadWorksContainerBasic__Format : roadWorksContainerBasic__Type t_Format

type rescueContainer__Type = { rescueContainer__lightBarSirenInUse : lightBarSirenInUse__Type }

val rescueContainer__list : seq_elem list

type rescueContainer__Format_Type = seq_elem_to_format * seq_elem_to_format

val rescueContainer__Format_list : rescueContainer__Format_Type

val rescueContainer__list__Format : seq_type t_Format

val rescueContainer__F1 :
  rescueContainer__Type -> lightBarSirenInUse__Type * unit

val rescueContainer__F2 : seq_type -> rescueContainer__Type

val rescueContainer__Format : rescueContainer__Type t_Format

type causeCodeType__Type = int

val causeCodeType__Format : int t_Format

type subCauseCodeType__Type = int

val subCauseCodeType__Format : int t_Format

type causeCode__Type = { causeCode__causeCode : causeCodeType__Type;
                         causeCode__subCauseCode : subCauseCodeType__Type }

val causeCode__root_list : seq_elem list

val causeCode__ext_list : typ list

type causeCode__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val causeCode__root_Format_list : causeCode__root_Format_Type

type causeCode__ext_Format_Type = unit t_Format

val causeCode__ext_Format_list : causeCode__ext_Format_Type

type causeCode__list_type = seq_type * seq_ext_type

val causeCode__list_format : causeCode__list_type t_Format

val causeCode__F1 : causeCode__Type -> causeCode__list_type

val causeCode__F2 : causeCode__list_type -> causeCode__Type

val causeCode__Format : causeCode__Type t_Format

type emergencyPriority__Type = bit_string_fixed

val emergencyPriority__Format : emergencyPriority__Type t_Format

type emergencyContainer__Type = { emergencyContainer__lightBarSirenInUse : 
                                  lightBarSirenInUse__Type;
                                  emergencyContainer__incidentIndication : 
                                  causeCode__Type option;
                                  emergencyContainer__emergencyPriority : 
                                  emergencyPriority__Type option }

val emergencyContainer__list : seq_elem list

type emergencyContainer__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val emergencyContainer__Format_list : emergencyContainer__Format_Type

val emergencyContainer__list__Format : seq_type t_Format

val emergencyContainer__F1 :
  emergencyContainer__Type -> lightBarSirenInUse__Type * (causeCode__Type
  option * (emergencyPriority__Type option * unit))

val emergencyContainer__F2 : seq_type -> emergencyContainer__Type

val emergencyContainer__Format : emergencyContainer__Type t_Format

type trafficRule__root__Type =
| TrafficRule__root__noPassing
| TrafficRule__root__noPassingForTrucks
| TrafficRule__root__passToRight
| TrafficRule__root__passToLeft

val trafficRule__root__nat__Format : int t_Format

val trafficRule__root__F1 : trafficRule__root__Type -> int

val trafficRule__root__F2 : int -> trafficRule__root__Type

type trafficRule__ext__Type = empty_set

type trafficRule__Type = (trafficRule__root__Type, trafficRule__ext__Type) sum

val trafficRule__root__Format : trafficRule__root__Type t_Format

val trafficRule__ext__Format : trafficRule__ext__Type t_Format

val trafficRule__Format : trafficRule__Type t_Format

type speedLimit__Type = int

val speedLimit__Format : int t_Format

type safetyCarContainer__Type = { safetyCarContainer__lightBarSirenInUse : 
                                  lightBarSirenInUse__Type;
                                  safetyCarContainer__incidentIndication : 
                                  causeCode__Type option;
                                  safetyCarContainer__trafficRule : trafficRule__Type
                                                                    option;
                                  safetyCarContainer__speedLimit : speedLimit__Type
                                                                   option }

val safetyCarContainer__list : seq_elem list

type safetyCarContainer__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

val safetyCarContainer__Format_list : safetyCarContainer__Format_Type

val safetyCarContainer__list__Format : seq_type t_Format

val safetyCarContainer__F1 :
  safetyCarContainer__Type -> lightBarSirenInUse__Type * (causeCode__Type
  option * (trafficRule__Type option * (speedLimit__Type option * unit)))

val safetyCarContainer__F2 : seq_type -> safetyCarContainer__Type

val safetyCarContainer__Format : safetyCarContainer__Type t_Format

type specialVehicleContainer__root__Type =
| SpecialVehicleContainer__root__publicTransportContainer of publicTransportContainer__Type
| SpecialVehicleContainer__root__specialTransportContainer of specialTransportContainer__Type
| SpecialVehicleContainer__root__dangerousGoodsContainer of dangerousGoodsContainer__Type
| SpecialVehicleContainer__root__roadWorksContainerBasic of roadWorksContainerBasic__Type
| SpecialVehicleContainer__root__rescueContainer of rescueContainer__Type
| SpecialVehicleContainer__root__emergencyContainer of emergencyContainer__Type
| SpecialVehicleContainer__root__safetyCarContainer of safetyCarContainer__Type

type specialVehicleContainer__ext__Type = empty_set

type specialVehicleContainer__Type =
  (specialVehicleContainer__root__Type, specialVehicleContainer__ext__Type) sum

val specialVehicleContainer__root__list__Format : (int, __) sigT t_Format

val specialVehicleContainer__root__F1 :
  specialVehicleContainer__root__Type -> choice

val specialVehicleContainer__root__F2 :
  choice -> specialVehicleContainer__root__Type

val specialVehicleContainer__root__Format :
  specialVehicleContainer__root__Type t_Format

val specialVehicleContainer__ext__Format :
  specialVehicleContainer__ext__Type t_Format

val specialVehicleContainer__Format : specialVehicleContainer__Type t_Format

type camParameters__Type = { camParameters__basicContainer : basicContainer__Type;
                             camParameters__highFrequencyContainer : highFrequencyContainer__Type;
                             camParameters__lowFrequencyContainer : lowFrequencyContainer__Type
                                                                    option;
                             camParameters__specialVehicleContainer : 
                             specialVehicleContainer__Type option }

val camParameters__root_list : seq_elem list

val camParameters__ext_list : typ list

type camParameters__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

val camParameters__root_Format_list : camParameters__root_Format_Type

type camParameters__ext_Format_Type = unit t_Format

val camParameters__ext_Format_list : camParameters__ext_Format_Type

type camParameters__list_type = seq_type * seq_ext_type

val camParameters__list_format : camParameters__list_type t_Format

val camParameters__F1 : camParameters__Type -> camParameters__list_type

val camParameters__F2 : camParameters__list_type -> camParameters__Type

val camParameters__Format : camParameters__Type t_Format

type coopAwareness__Type = { coopAwareness__generationDeltaTime : generationDeltaTime__Type;
                             coopAwareness__camParameters : camParameters__Type }

val coopAwareness__list : seq_elem list

type coopAwareness__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val coopAwareness__Format_list : coopAwareness__Format_Type

val coopAwareness__list__Format : seq_type t_Format

val coopAwareness__F1 :
  coopAwareness__Type ->
  generationDeltaTime__Type * (camParameters__Type * unit)

val coopAwareness__F2 : seq_type -> coopAwareness__Type

val coopAwareness__Format : coopAwareness__Type t_Format

type cAM__Type = { cAM__header : itsPduHeader__Type;
                   cAM__cam : coopAwareness__Type }

val cAM__list : seq_elem list

type cAM__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val cAM__Format_list : cAM__Format_Type

val cAM__list__Format : seq_type t_Format

val cAM__F1 : cAM__Type -> itsPduHeader__Type * (coopAwareness__Type * unit)

val cAM__F2 : seq_type -> cAM__Type

val cAM__Format : cAM__Type t_Format

type sequenceNumber__Type = int

val sequenceNumber__Format : int t_Format

type actionID__Type = { actionID__originatingStationID : stationID__Type;
                        actionID__sequenceNumber : sequenceNumber__Type }

val actionID__list : seq_elem list

type actionID__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val actionID__Format_list : actionID__Format_Type

val actionID__list__Format : seq_type t_Format

val actionID__F1 :
  actionID__Type -> stationID__Type * (sequenceNumber__Type * unit)

val actionID__F2 : seq_type -> actionID__Type

val actionID__Format : actionID__Type t_Format

type termination__Type =
| Termination__isCancellation
| Termination__isNegation

val termination__nat__Format : int t_Format

val termination__F1 : termination__Type -> int

val termination__F2 : int -> termination__Type

val termination__Format : termination__Type t_Format

type relevanceDistance__Type =
| RelevanceDistance__lessThan50m
| RelevanceDistance__lessThan100m
| RelevanceDistance__lessThan200m
| RelevanceDistance__lessThan500m
| RelevanceDistance__lessThan1000m
| RelevanceDistance__lessThan5km
| RelevanceDistance__lessThan10km
| RelevanceDistance__over10km

val relevanceDistance__nat__Format : int t_Format

val relevanceDistance__F1 : relevanceDistance__Type -> int

val relevanceDistance__F2 : int -> relevanceDistance__Type

val relevanceDistance__Format : relevanceDistance__Type t_Format

type relevanceTrafficDirection__Type =
| RelevanceTrafficDirection__allTrafficDirections
| RelevanceTrafficDirection__upstreamTraffic
| RelevanceTrafficDirection__downstreamTraffic
| RelevanceTrafficDirection__oppositeTraffic

val relevanceTrafficDirection__nat__Format : int t_Format

val relevanceTrafficDirection__F1 : relevanceTrafficDirection__Type -> int

val relevanceTrafficDirection__F2 : int -> relevanceTrafficDirection__Type

val relevanceTrafficDirection__Format :
  relevanceTrafficDirection__Type t_Format

type validityDuration__Type = int

val validityDuration__Format : int t_Format

type transmissionInterval__Type = int

val transmissionInterval__Format : int t_Format

type managementContainer__Type = { managementContainer__actionID : actionID__Type;
                                   managementContainer__detectionTime : 
                                   timestampIts__Type;
                                   managementContainer__referenceTime : 
                                   timestampIts__Type;
                                   managementContainer__termination : 
                                   termination__Type option;
                                   managementContainer__eventPosition : 
                                   referencePosition__Type;
                                   managementContainer__relevanceDistance : 
                                   relevanceDistance__Type option;
                                   managementContainer__relevanceTrafficDirection : 
                                   relevanceTrafficDirection__Type option;
                                   managementContainer__validityDuration : 
                                   validityDuration__Type;
                                   managementContainer__transmissionInterval : 
                                   transmissionInterval__Type option;
                                   managementContainer__stationType : 
                                   stationType__Type }

val managementContainer__root_list : seq_elem list

val managementContainer__ext_list : typ list

type managementContainer__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))))))))

val managementContainer__root_Format_list :
  managementContainer__root_Format_Type

type managementContainer__ext_Format_Type = unit t_Format

val managementContainer__ext_Format_list : managementContainer__ext_Format_Type

type managementContainer__list_type = seq_type * seq_ext_type

val managementContainer__list_format : managementContainer__list_type t_Format

val managementContainer__F1 :
  managementContainer__Type -> managementContainer__list_type

val managementContainer__F2 :
  managementContainer__list_type -> managementContainer__Type

val managementContainer__Format : managementContainer__Type t_Format

type informationQuality__Type = int

val informationQuality__Format : int t_Format

type eventPoint__Type = { eventPoint__eventPosition : deltaReferencePosition__Type;
                          eventPoint__eventDeltaTime : pathDeltaTime__Type
                                                       option;
                          eventPoint__informationQuality : informationQuality__Type }

val eventPoint__list : seq_elem list

type eventPoint__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val eventPoint__Format_list : eventPoint__Format_Type

val eventPoint__list__Format : seq_type t_Format

val eventPoint__F1 :
  eventPoint__Type -> deltaReferencePosition__Type * (pathDeltaTime__Type
  option * (informationQuality__Type * unit))

val eventPoint__F2 : seq_type -> eventPoint__Type

val eventPoint__Format : eventPoint__Type t_Format

type eventHistory__Type = eventPoint__Type list

val eventHistory__Format : eventHistory__Type t_Format

type situationContainer__Type = { situationContainer__informationQuality : 
                                  informationQuality__Type;
                                  situationContainer__eventType : causeCode__Type;
                                  situationContainer__linkedCause : causeCode__Type
                                                                    option;
                                  situationContainer__eventHistory : eventHistory__Type
                                                                     option }

val situationContainer__root_list : seq_elem list

val situationContainer__ext_list : typ list

type situationContainer__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

val situationContainer__root_Format_list : situationContainer__root_Format_Type

type situationContainer__ext_Format_Type = unit t_Format

val situationContainer__ext_Format_list : situationContainer__ext_Format_Type

type situationContainer__list_type = seq_type * seq_ext_type

val situationContainer__list_format : situationContainer__list_type t_Format

val situationContainer__F1 :
  situationContainer__Type -> situationContainer__list_type

val situationContainer__F2 :
  situationContainer__list_type -> situationContainer__Type

val situationContainer__Format : situationContainer__Type t_Format

type traces__Type = pathHistory__Type list

val traces__Format : traces__Type t_Format

type roadType__Type =
| RoadType__urban_NoStructuralSeparationToOppositeLanes
| RoadType__urban_WithStructuralSeparationToOppositeLanes
| RoadType__nonUrban_NoStructuralSeparationToOppositeLanes
| RoadType__nonUrban_WithStructuralSeparationToOppositeLanes

val roadType__nat__Format : int t_Format

val roadType__F1 : roadType__Type -> int

val roadType__F2 : int -> roadType__Type

val roadType__Format : roadType__Type t_Format

type locationContainer__Type = { locationContainer__eventSpeed : speed__Type
                                                                 option;
                                 locationContainer__eventPositionHeading : 
                                 heading__Type option;
                                 locationContainer__traces : traces__Type;
                                 locationContainer__roadType : roadType__Type
                                                               option }

val locationContainer__root_list : seq_elem list

val locationContainer__ext_list : typ list

type locationContainer__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

val locationContainer__root_Format_list : locationContainer__root_Format_Type

type locationContainer__ext_Format_Type = unit t_Format

val locationContainer__ext_Format_list : locationContainer__ext_Format_Type

type locationContainer__list_type = seq_type * seq_ext_type

val locationContainer__list_format : locationContainer__list_type t_Format

val locationContainer__F1 :
  locationContainer__Type -> locationContainer__list_type

val locationContainer__F2 :
  locationContainer__list_type -> locationContainer__Type

val locationContainer__Format : locationContainer__Type t_Format

type heightLonCarr__Type = int

val heightLonCarr__Format : int t_Format

type posLonCarr__Type = int

val posLonCarr__Format : int t_Format

type posPillar__Type = int

val posPillar__Format : int t_Format

type positionOfPillars__Type = posPillar__Type list

val positionOfPillars__Format : positionOfPillars__Type t_Format

type posCentMass__Type = int

val posCentMass__Format : int t_Format

type wheelBaseVehicle__Type = int

val wheelBaseVehicle__Format : int t_Format

type turningRadius__Type = int

val turningRadius__Format : int t_Format

type posFrontAx__Type = int

val posFrontAx__Format : int t_Format

type positionOfOccupants__Type = bit_string_fixed

val positionOfOccupants__Format : positionOfOccupants__Type t_Format

type vehicleMass__Type = int

val vehicleMass__Format : int t_Format

type requestResponseIndication__Type =
| RequestResponseIndication__request
| RequestResponseIndication__response

val requestResponseIndication__nat__Format : int t_Format

val requestResponseIndication__F1 : requestResponseIndication__Type -> int

val requestResponseIndication__F2 : int -> requestResponseIndication__Type

val requestResponseIndication__Format :
  requestResponseIndication__Type t_Format

type impactReductionContainer__Type = { impactReductionContainer__heightLonCarrLeft : 
                                        heightLonCarr__Type;
                                        impactReductionContainer__heightLonCarrRight : 
                                        heightLonCarr__Type;
                                        impactReductionContainer__posLonCarrLeft : 
                                        posLonCarr__Type;
                                        impactReductionContainer__posLonCarrRight : 
                                        posLonCarr__Type;
                                        impactReductionContainer__positionOfPillars : 
                                        positionOfPillars__Type;
                                        impactReductionContainer__posCentMass : 
                                        posCentMass__Type;
                                        impactReductionContainer__wheelBaseVehicle : 
                                        wheelBaseVehicle__Type;
                                        impactReductionContainer__turningRadius : 
                                        turningRadius__Type;
                                        impactReductionContainer__posFrontAx : 
                                        posFrontAx__Type;
                                        impactReductionContainer__positionOfOccupants : 
                                        positionOfOccupants__Type;
                                        impactReductionContainer__vehicleMass : 
                                        vehicleMass__Type;
                                        impactReductionContainer__requestResponseIndication : 
                                        requestResponseIndication__Type }

val impactReductionContainer__list : seq_elem list

type impactReductionContainer__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))))))))))

val impactReductionContainer__Format_list :
  impactReductionContainer__Format_Type

val impactReductionContainer__list__Format : seq_type t_Format

val impactReductionContainer__F1 :
  impactReductionContainer__Type ->
  heightLonCarr__Type * (heightLonCarr__Type * (posLonCarr__Type * (posLonCarr__Type * (positionOfPillars__Type * (posCentMass__Type * (wheelBaseVehicle__Type * (turningRadius__Type * (posFrontAx__Type * (positionOfOccupants__Type * (vehicleMass__Type * (requestResponseIndication__Type * unit)))))))))))

val impactReductionContainer__F2 : seq_type -> impactReductionContainer__Type

val impactReductionContainer__Format : impactReductionContainer__Type t_Format

type temperature__Type = int

val temperature__Format : int t_Format

type restrictedTypes__Type = stationType__Type list

val restrictedTypes__Format : restrictedTypes__Type t_Format

type itineraryPath__Type = referencePosition__Type list

val itineraryPath__Format : itineraryPath__Type t_Format

type referenceDenms__Type = actionID__Type list

val referenceDenms__Format : referenceDenms__Type t_Format

type roadWorksContainerExtended__Type = { roadWorksContainerExtended__lightBarSirenInUse : 
                                          lightBarSirenInUse__Type option;
                                          roadWorksContainerExtended__closedLanes : 
                                          closedLanes__Type option;
                                          roadWorksContainerExtended__restriction : 
                                          restrictedTypes__Type option;
                                          roadWorksContainerExtended__speedLimit : 
                                          speedLimit__Type option;
                                          roadWorksContainerExtended__incidentIndication : 
                                          causeCode__Type option;
                                          roadWorksContainerExtended__recommendedPath : 
                                          itineraryPath__Type option;
                                          roadWorksContainerExtended__startingPointSpeedLimit : 
                                          deltaReferencePosition__Type option;
                                          roadWorksContainerExtended__trafficFlowRule : 
                                          trafficRule__Type option;
                                          roadWorksContainerExtended__referenceDenms : 
                                          referenceDenms__Type option }

val roadWorksContainerExtended__list : seq_elem list

type roadWorksContainerExtended__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))))))))

val roadWorksContainerExtended__Format_list :
  roadWorksContainerExtended__Format_Type

val roadWorksContainerExtended__list__Format : seq_type t_Format

val roadWorksContainerExtended__F1 :
  roadWorksContainerExtended__Type -> lightBarSirenInUse__Type
  option * (closedLanes__Type option * (restrictedTypes__Type
  option * (speedLimit__Type option * (causeCode__Type
  option * (itineraryPath__Type option * (deltaReferencePosition__Type
  option * (trafficRule__Type option * (referenceDenms__Type
  option * unit))))))))

val roadWorksContainerExtended__F2 :
  seq_type -> roadWorksContainerExtended__Type

val roadWorksContainerExtended__Format :
  roadWorksContainerExtended__Type t_Format

type positioningSolutionType__root__Type =
| PositioningSolutionType__root__noPositioningSolution
| PositioningSolutionType__root__sGNSS
| PositioningSolutionType__root__dGNSS
| PositioningSolutionType__root__sGNSSplusDR
| PositioningSolutionType__root__dGNSSplusDR
| PositioningSolutionType__root__dR

val positioningSolutionType__root__nat__Format : int t_Format

val positioningSolutionType__root__F1 :
  positioningSolutionType__root__Type -> int

val positioningSolutionType__root__F2 :
  int -> positioningSolutionType__root__Type

type positioningSolutionType__ext__Type = empty_set

type positioningSolutionType__Type =
  (positioningSolutionType__root__Type, positioningSolutionType__ext__Type) sum

val positioningSolutionType__root__Format :
  positioningSolutionType__root__Type t_Format

val positioningSolutionType__ext__Format :
  positioningSolutionType__ext__Type t_Format

val positioningSolutionType__Format : positioningSolutionType__Type t_Format

type stationarySince__Type =
| StationarySince__lessThan1Minute
| StationarySince__lessThan2Minutes
| StationarySince__lessThan15Minutes
| StationarySince__equalOrGreater15Minutes

val stationarySince__nat__Format : int t_Format

val stationarySince__F1 : stationarySince__Type -> int

val stationarySince__F2 : int -> stationarySince__Type

val stationarySince__Format : stationarySince__Type t_Format

type phoneNumber__Type = char_list

val phoneNumber__Format : phoneNumber__Type t_Format

type dangerousGoodsExtended__emergencyActionCode__Type = char_list

type dangerousGoodsExtended__Type = { dangerousGoodsExtended__dangerousGoodsType : 
                                      dangerousGoodsBasic__Type;
                                      dangerousGoodsExtended__unNumber : 
                                      int;
                                      dangerousGoodsExtended__elevatedTemperature : 
                                      bool;
                                      dangerousGoodsExtended__tunnelsRestricted : 
                                      bool;
                                      dangerousGoodsExtended__limitedQuantity : 
                                      bool;
                                      dangerousGoodsExtended__emergencyActionCode : 
                                      dangerousGoodsExtended__emergencyActionCode__Type
                                      option;
                                      dangerousGoodsExtended__phoneNumber : 
                                      phoneNumber__Type option;
                                      dangerousGoodsExtended__companyName : 
                                      string option }

val dangerousGoodsExtended__root_list : seq_elem list

val dangerousGoodsExtended__ext_list : typ list

val dangerousGoodsExtended__unNumber__Format : int t_Format

val dangerousGoodsExtended__emergencyActionCode__Format :
  dangerousGoodsExtended__emergencyActionCode__Type t_Format

type dangerousGoodsExtended__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))))))

val dangerousGoodsExtended__root_Format_list :
  dangerousGoodsExtended__root_Format_Type

type dangerousGoodsExtended__ext_Format_Type = unit t_Format

val dangerousGoodsExtended__ext_Format_list :
  dangerousGoodsExtended__ext_Format_Type

type dangerousGoodsExtended__list_type = seq_type * seq_ext_type

val dangerousGoodsExtended__list_format :
  dangerousGoodsExtended__list_type t_Format

val dangerousGoodsExtended__F1 :
  dangerousGoodsExtended__Type -> dangerousGoodsExtended__list_type

val dangerousGoodsExtended__F2 :
  dangerousGoodsExtended__list_type -> dangerousGoodsExtended__Type

val dangerousGoodsExtended__Format : dangerousGoodsExtended__Type t_Format

type numberOfOccupants__Type = int

val numberOfOccupants__Format : int t_Format

type wMInumber__Type = char_list

val wMInumber__Format : wMInumber__Type t_Format

type vDS__Type = char_list

val vDS__Format : vDS__Type t_Format

type vehicleIdentification__Type = { vehicleIdentification__wMInumber : 
                                     wMInumber__Type option;
                                     vehicleIdentification__vDS : vDS__Type
                                                                  option }

val vehicleIdentification__root_list : seq_elem list

val vehicleIdentification__ext_list : typ list

type vehicleIdentification__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val vehicleIdentification__root_Format_list :
  vehicleIdentification__root_Format_Type

type vehicleIdentification__ext_Format_Type = unit t_Format

val vehicleIdentification__ext_Format_list :
  vehicleIdentification__ext_Format_Type

type vehicleIdentification__list_type = seq_type * seq_ext_type

val vehicleIdentification__list_format :
  vehicleIdentification__list_type t_Format

val vehicleIdentification__F1 :
  vehicleIdentification__Type -> vehicleIdentification__list_type

val vehicleIdentification__F2 :
  vehicleIdentification__list_type -> vehicleIdentification__Type

val vehicleIdentification__Format : vehicleIdentification__Type t_Format

type energyStorageType__Type = bit_string_fixed

val energyStorageType__Format : energyStorageType__Type t_Format

type stationaryVehicleContainer__Type = { stationaryVehicleContainer__stationarySince : 
                                          stationarySince__Type option;
                                          stationaryVehicleContainer__stationaryCause : 
                                          causeCode__Type option;
                                          stationaryVehicleContainer__carryingDangerousGoods : 
                                          dangerousGoodsExtended__Type option;
                                          stationaryVehicleContainer__numberOfOccupants : 
                                          numberOfOccupants__Type option;
                                          stationaryVehicleContainer__vehicleIdentification : 
                                          vehicleIdentification__Type option;
                                          stationaryVehicleContainer__energyStorageType : 
                                          energyStorageType__Type option }

val stationaryVehicleContainer__list : seq_elem list

type stationaryVehicleContainer__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))))

val stationaryVehicleContainer__Format_list :
  stationaryVehicleContainer__Format_Type

val stationaryVehicleContainer__list__Format : seq_type t_Format

val stationaryVehicleContainer__F1 :
  stationaryVehicleContainer__Type -> stationarySince__Type
  option * (causeCode__Type option * (dangerousGoodsExtended__Type
  option * (numberOfOccupants__Type option * (vehicleIdentification__Type
  option * (energyStorageType__Type option * unit)))))

val stationaryVehicleContainer__F2 :
  seq_type -> stationaryVehicleContainer__Type

val stationaryVehicleContainer__Format :
  stationaryVehicleContainer__Type t_Format

type alacarteContainer__Type = { alacarteContainer__lanePosition : lanePosition__Type
                                                                   option;
                                 alacarteContainer__impactReduction : 
                                 impactReductionContainer__Type option;
                                 alacarteContainer__externalTemperature : 
                                 temperature__Type option;
                                 alacarteContainer__roadWorks : roadWorksContainerExtended__Type
                                                                option;
                                 alacarteContainer__positioningSolution : 
                                 positioningSolutionType__Type option;
                                 alacarteContainer__stationaryVehicle : 
                                 stationaryVehicleContainer__Type option }

val alacarteContainer__root_list : seq_elem list

val alacarteContainer__ext_list : typ list

type alacarteContainer__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))))

val alacarteContainer__root_Format_list : alacarteContainer__root_Format_Type

type alacarteContainer__ext_Format_Type = unit t_Format

val alacarteContainer__ext_Format_list : alacarteContainer__ext_Format_Type

type alacarteContainer__list_type = seq_type * seq_ext_type

val alacarteContainer__list_format : alacarteContainer__list_type t_Format

val alacarteContainer__F1 :
  alacarteContainer__Type -> alacarteContainer__list_type

val alacarteContainer__F2 :
  alacarteContainer__list_type -> alacarteContainer__Type

val alacarteContainer__Format : alacarteContainer__Type t_Format

type decentralizedEnvironmentalNotificationMessage__Type = { decentralizedEnvironmentalNotificationMessage__management : 
                                                             managementContainer__Type;
                                                             decentralizedEnvironmentalNotificationMessage__situation : 
                                                             situationContainer__Type
                                                             option;
                                                             decentralizedEnvironmentalNotificationMessage__location : 
                                                             locationContainer__Type
                                                             option;
                                                             decentralizedEnvironmentalNotificationMessage__alacarte : 
                                                             alacarteContainer__Type
                                                             option }

val decentralizedEnvironmentalNotificationMessage__list : seq_elem list

type decentralizedEnvironmentalNotificationMessage__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

val decentralizedEnvironmentalNotificationMessage__Format_list :
  decentralizedEnvironmentalNotificationMessage__Format_Type

val decentralizedEnvironmentalNotificationMessage__list__Format :
  seq_type t_Format

val decentralizedEnvironmentalNotificationMessage__F1 :
  decentralizedEnvironmentalNotificationMessage__Type ->
  managementContainer__Type * (situationContainer__Type
  option * (locationContainer__Type option * (alacarteContainer__Type
  option * unit)))

val decentralizedEnvironmentalNotificationMessage__F2 :
  seq_type -> decentralizedEnvironmentalNotificationMessage__Type

val decentralizedEnvironmentalNotificationMessage__Format :
  decentralizedEnvironmentalNotificationMessage__Type t_Format

type dENM__Type = { dENM__header : itsPduHeader__Type;
                    dENM__denm : decentralizedEnvironmentalNotificationMessage__Type }

val dENM__list : seq_elem list

type dENM__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val dENM__Format_list : dENM__Format_Type

val dENM__list__Format : seq_type t_Format

val dENM__F1 :
  dENM__Type ->
  itsPduHeader__Type * (decentralizedEnvironmentalNotificationMessage__Type * unit)

val dENM__F2 : seq_type -> dENM__Type

val dENM__Format : dENM__Type t_Format
