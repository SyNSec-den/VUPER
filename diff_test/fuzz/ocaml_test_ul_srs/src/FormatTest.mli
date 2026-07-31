
type __ = Obj.t

type empty_set = |

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



val pow : int -> int -> int



module Nat :
 sig
  val pred : int -> int

  val add : int -> int -> int

  val double : int -> int

  val shiftl : int -> int -> int
 end

module Pos :
 sig
  val succ : int -> int

  val add : int -> int -> int

  val add_carry : int -> int -> int

  val pred_double : int -> int

  val compare_cont : comparison -> int -> int -> comparison

  val compare : int -> int -> comparison

  val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1

  val to_nat : int -> int

  val of_succ_nat : int -> int

  val eq_dec : int -> int -> bool
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

  val compare : int -> int -> comparison
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

val choose_len_det_helper3 : bool -> int -> bool

val choose_len_det_format : bool -> int t_Format

val bit_len_format : (bool * int) t_Format

val uncons_len_det_format : int t_Format

val choose_norm_small_det : bool -> int t_Format

val bit_norm_small_len_format : (bool * int) t_Format

val normally_small_len_det_format : int t_Format

val small_enc : int serialize

val small_dec : int parse

val z_range_dec : int -> int -> int -> bool

val ranged_int_format : int -> int -> int t_Format

val of_nat_non_opt : int -> char

val byte_format : char t_Format

val byte_list_format : int -> char list t_Format

type octet_string = char list

val octet_string_no_cons_format : char list t_Format

val octet_string_ranged_format : int -> int -> char list t_Format

val octet_string_fixed_format : int -> char list t_Format

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

val seq_of_format : 'a1 t_Format -> int -> int -> 'a1 list t_Format

val seq_of_fixed_format : 'a1 t_Format -> int -> 'a1 list t_Format

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

val octet_string_nc__Format : char list t_Format

val sum_serial : 'a1 serialize -> 'a2 serialize -> ('a1, 'a2) sum serialize

val sum_parse : 'a1 parse -> 'a2 parse -> ('a1, 'a2) sum parse

val sum_to_len :
  ('a1 -> int option) -> ('a2 -> int option) -> ('a1, 'a2) sum -> int option

val sum_format : 'a1 t_Format -> 'a2 t_Format -> ('a1, 'a2) sum t_Format

val restrict_add_serialize : ('a1 -> bool) -> 'a1 serialize -> 'a1 serialize

val restrict_add_parse : ('a1 -> bool) -> 'a1 parse -> 'a1 parse

val restrict_add_format : ('a1 -> bool) -> 'a1 t_Format -> 'a1 t_Format

val maxBT_IdReport_r16 : int

val maxCellHistory_r16 : int

val maxPSCellHistory_r17 : int

val maxCellMeasIdle_r16 : int

val maxEARFCN : int

val maxLogMeasReport_r16 : int

val maxMultiBands : int

val maxNARFCN : int

val maxFreqIdle_r16 : int

val maxNrofServingCells : int

val maxNrofServingCells_1 : int

val maxNrofAppLayerMeas_r17 : int

val maxNrofAppLayerMeas_1_r17 : int

val maxNrofSL_RxInfoSet_r17 : int

val maxNrofCondCells_r16 : int

val maxNrofPDU_Sessions_r17 : int

val maxLC_ID : int

val maxNrofBWPs : int

val maxNrofPhysicalResourceBlocks_1 : int

val maxNrofFreqSL_r16 : int

val maxNrofSL_PoolToMeasureNR_r16 : int

val maxNrofSL_QFIs_r16 : int

val maxNrofSL_QFIsPerDest_r16 : int

val maxPLMN : int

val maxTAC_r17 : int

val maxNrofCSI_RS_ResourcesRRM_1 : int

val maxNrofMeasId : int

val maxNrofSL_Dest_r16 : int

val maxNrofSLRB_r16 : int

val maxNrofPoolID_r16 : int

val maxNrofSRS_Resources_1 : int

val maxNrofSRS_PosResources_r16 : int

val maxNrofSRS_PosResources_1_r16 : int

val maxRAT_CapabilityContainers : int

val maxNrofTrafficPattern_r16 : int

val maxBands : int

val maxBandsEUTRA : int

val maxCellReport : int

val maxDRB : int

val maxFreq : int

val maxFreqLayers : int

val maxFreqIDC_r16 : int

val maxCombIDC_r16 : int

val maxNrofIndexesToReport : int

val maxNrofIndexesToReport2 : int

val maxNrofSSBs_r16 : int

val maxNrofSSBs_1 : int

val maxNrofS_NSSAI : int

val maxNrofUL_Allocations : int

val maxSecondaryCellGroups : int

val maxNrofServingCellsEUTRA : int

val maxNrofMultiBands : int

val maxCellSFTD : int

val maxSIB : int

val maxInterRAT_RSTD_Freq : int

val maxNPN_r16 : int

val maxOnDemandSIB_r16 : int

val maxOnDemandPosSIB_r16 : int

val maxWLAN_Id_Report_r16 : int

val maxRAReport_r16 : int

val maxNrofCLI_RSSI_Resources_1_r16 : int

val maxCLI_Report_r16 : int

val maxNrofCC_Group_r17 : int

val maxNrOfTxTEGReport_r17 : int

val maxNrOfTxTEG_ID_1_r17 : int

val maxNrofReqComDC_Location_r17 : int

val maxNrofTxDC_TwoCarrier_r16 : int

val maxCEFReport_r17 : int

val maxFreqMBS_r17 : int

val maxNrofMBS_ServiceListPerUE_r17 : int

type measId__Type = int

val measId__Format : int t_Format

type servCellIndex__Type = int

val servCellIndex__Format : int t_Format

type physCellId__Type = int

val physCellId__Format : int t_Format

type rSRP_Range__Type = int

val rSRP_Range__Format : int t_Format

type rSRQ_Range__Type = int

val rSRQ_Range__Format : int t_Format

type sINR_Range__Type = int

val sINR_Range__Format : int t_Format

type measQuantityResults__Type = { measQuantityResults__rsrp : rSRP_Range__Type
                                                               option;
                                   measQuantityResults__rsrq : rSRQ_Range__Type
                                                               option;
                                   measQuantityResults__sinr : sINR_Range__Type
                                                               option }

val measQuantityResults__list : seq_elem list

type measQuantityResults__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val measQuantityResults__Format_list : measQuantityResults__Format_Type

val measQuantityResults__list__Format : seq_type t_Format

val measQuantityResults__F1 :
  measQuantityResults__Type -> rSRP_Range__Type option * (rSRQ_Range__Type
  option * (sINR_Range__Type option * unit))

val measQuantityResults__F2 : seq_type -> measQuantityResults__Type

val measQuantityResults__Format : measQuantityResults__Type t_Format

type sSB_Index__Type = int

val sSB_Index__Format : int t_Format

type resultsPerSSB_Index__Type = { resultsPerSSB_Index__ssb_Index : sSB_Index__Type;
                                   resultsPerSSB_Index__ssb_Results : 
                                   measQuantityResults__Type option }

val resultsPerSSB_Index__list : seq_elem list

type resultsPerSSB_Index__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val resultsPerSSB_Index__Format_list : resultsPerSSB_Index__Format_Type

val resultsPerSSB_Index__list__Format : seq_type t_Format

val resultsPerSSB_Index__F1 :
  resultsPerSSB_Index__Type -> sSB_Index__Type * (measQuantityResults__Type
  option * unit)

val resultsPerSSB_Index__F2 : seq_type -> resultsPerSSB_Index__Type

val resultsPerSSB_Index__Format : resultsPerSSB_Index__Type t_Format

type resultsPerSSB_IndexList__Type = resultsPerSSB_Index__Type list

val resultsPerSSB_IndexList__Format : resultsPerSSB_IndexList__Type t_Format

type cSI_RS_Index__Type = int

val cSI_RS_Index__Format : int t_Format

type resultsPerCSI_RS_Index__Type = { resultsPerCSI_RS_Index__csi_RS_Index : 
                                      cSI_RS_Index__Type;
                                      resultsPerCSI_RS_Index__csi_RS_Results : 
                                      measQuantityResults__Type option }

val resultsPerCSI_RS_Index__list : seq_elem list

type resultsPerCSI_RS_Index__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val resultsPerCSI_RS_Index__Format_list : resultsPerCSI_RS_Index__Format_Type

val resultsPerCSI_RS_Index__list__Format : seq_type t_Format

val resultsPerCSI_RS_Index__F1 :
  resultsPerCSI_RS_Index__Type ->
  cSI_RS_Index__Type * (measQuantityResults__Type option * unit)

val resultsPerCSI_RS_Index__F2 : seq_type -> resultsPerCSI_RS_Index__Type

val resultsPerCSI_RS_Index__Format : resultsPerCSI_RS_Index__Type t_Format

type resultsPerCSI_RS_IndexList__Type = resultsPerCSI_RS_Index__Type list

val resultsPerCSI_RS_IndexList__Format :
  resultsPerCSI_RS_IndexList__Type t_Format

type mCC_MNC_Digit__Type = int

val mCC_MNC_Digit__Format : int t_Format

type mCC__Type = mCC_MNC_Digit__Type list

val mCC__Format : mCC__Type t_Format

type mNC__Type = mCC_MNC_Digit__Type list

val mNC__Format : mNC__Type t_Format

type pLMN_Identity__Type = { pLMN_Identity__mcc : mCC__Type option;
                             pLMN_Identity__mnc : mNC__Type }

val pLMN_Identity__list : seq_elem list

type pLMN_Identity__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val pLMN_Identity__Format_list : pLMN_Identity__Format_Type

val pLMN_Identity__list__Format : seq_type t_Format

val pLMN_Identity__F1 :
  pLMN_Identity__Type -> mCC__Type option * (mNC__Type * unit)

val pLMN_Identity__F2 : seq_type -> pLMN_Identity__Type

val pLMN_Identity__Format : pLMN_Identity__Type t_Format

type trackingAreaCode__Type = bit_string_fixed

val trackingAreaCode__Format : trackingAreaCode__Type t_Format

type rAN_AreaCode__Type = int

val rAN_AreaCode__Format : int t_Format

type cellIdentity__Type = bit_string_fixed

val cellIdentity__Format : cellIdentity__Type t_Format

type pLMN_IdentityInfo__plmn_IdentityList__Type = pLMN_Identity__Type list

type pLMN_IdentityInfo__cellReservedForOperatorUse__Type =
| PLMN_IdentityInfo__cellReservedForOperatorUse__reserved
| PLMN_IdentityInfo__cellReservedForOperatorUse__notReserved

val pLMN_IdentityInfo__cellReservedForOperatorUse__nat__Format : int t_Format

val pLMN_IdentityInfo__cellReservedForOperatorUse__F1 :
  pLMN_IdentityInfo__cellReservedForOperatorUse__Type -> int

val pLMN_IdentityInfo__cellReservedForOperatorUse__F2 :
  int -> pLMN_IdentityInfo__cellReservedForOperatorUse__Type

type pLMN_IdentityInfo__ext0O__iab_Support_r16__Type =
| PLMN_IdentityInfo__ext0O__iab_Support_r16__true

val pLMN_IdentityInfo__ext0O__iab_Support_r16__nat__Format : int t_Format

val pLMN_IdentityInfo__ext0O__iab_Support_r16__F1 :
  pLMN_IdentityInfo__ext0O__iab_Support_r16__Type -> int

val pLMN_IdentityInfo__ext0O__iab_Support_r16__F2 :
  int -> pLMN_IdentityInfo__ext0O__iab_Support_r16__Type

type pLMN_IdentityInfo__ext0O__Type = { pLMN_IdentityInfo__ext0O__iab_Support_r16 : 
                                        pLMN_IdentityInfo__ext0O__iab_Support_r16__Type
                                        option }

val pLMN_IdentityInfo__ext0O__list : seq_elem list

type pLMN_IdentityInfo__ext0__Type = pLMN_IdentityInfo__ext0O__Type

type pLMN_IdentityInfo__ext1O__trackingAreaList_r17__Type =
  trackingAreaCode__Type list

type pLMN_IdentityInfo__ext1O__Type = { pLMN_IdentityInfo__ext1O__trackingAreaList_r17 : 
                                        pLMN_IdentityInfo__ext1O__trackingAreaList_r17__Type
                                        option;
                                        pLMN_IdentityInfo__ext1O__gNB_ID_Length_r17 : 
                                        int option }

val pLMN_IdentityInfo__ext1O__list : seq_elem list

type pLMN_IdentityInfo__ext1__Type = pLMN_IdentityInfo__ext1O__Type

type pLMN_IdentityInfo__Type = { pLMN_IdentityInfo__plmn_IdentityList : 
                                 pLMN_IdentityInfo__plmn_IdentityList__Type;
                                 pLMN_IdentityInfo__trackingAreaCode : 
                                 trackingAreaCode__Type option;
                                 pLMN_IdentityInfo__ranac : rAN_AreaCode__Type
                                                            option;
                                 pLMN_IdentityInfo__cellIdentity : cellIdentity__Type;
                                 pLMN_IdentityInfo__cellReservedForOperatorUse : 
                                 pLMN_IdentityInfo__cellReservedForOperatorUse__Type;
                                 pLMN_IdentityInfo__ext0 : pLMN_IdentityInfo__ext0__Type
                                                           option;
                                 pLMN_IdentityInfo__ext1 : pLMN_IdentityInfo__ext1__Type
                                                           option }

val pLMN_IdentityInfo__root_list : seq_elem list

val pLMN_IdentityInfo__ext_list : typ list

val pLMN_IdentityInfo__plmn_IdentityList__Format :
  pLMN_IdentityInfo__plmn_IdentityList__Type t_Format

val pLMN_IdentityInfo__cellReservedForOperatorUse__Format :
  pLMN_IdentityInfo__cellReservedForOperatorUse__Type t_Format

val pLMN_IdentityInfo__ext0O__iab_Support_r16__Format :
  pLMN_IdentityInfo__ext0O__iab_Support_r16__Type t_Format

type pLMN_IdentityInfo__ext0O__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val pLMN_IdentityInfo__ext0O__Format_list :
  pLMN_IdentityInfo__ext0O__Format_Type

val pLMN_IdentityInfo__ext0O__list__Format : seq_type t_Format

val pLMN_IdentityInfo__ext0O__F1 :
  pLMN_IdentityInfo__ext0O__Type ->
  pLMN_IdentityInfo__ext0O__iab_Support_r16__Type option * unit

val pLMN_IdentityInfo__ext0O__F2 : seq_type -> pLMN_IdentityInfo__ext0O__Type

val pLMN_IdentityInfo__ext0O__Format : pLMN_IdentityInfo__ext0O__Type t_Format

val pLMN_IdentityInfo__ext0__check_all_none :
  pLMN_IdentityInfo__ext0O__Type -> bool

val pLMN_IdentityInfo__ext0__Format : pLMN_IdentityInfo__ext0__Type t_Format

val pLMN_IdentityInfo__ext1O__trackingAreaList_r17__Format :
  pLMN_IdentityInfo__ext1O__trackingAreaList_r17__Type t_Format

val pLMN_IdentityInfo__ext1O__gNB_ID_Length_r17__Format : int t_Format

type pLMN_IdentityInfo__ext1O__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val pLMN_IdentityInfo__ext1O__Format_list :
  pLMN_IdentityInfo__ext1O__Format_Type

val pLMN_IdentityInfo__ext1O__list__Format : seq_type t_Format

val pLMN_IdentityInfo__ext1O__F1 :
  pLMN_IdentityInfo__ext1O__Type ->
  pLMN_IdentityInfo__ext1O__trackingAreaList_r17__Type option * (int
  option * unit)

val pLMN_IdentityInfo__ext1O__F2 : seq_type -> pLMN_IdentityInfo__ext1O__Type

val pLMN_IdentityInfo__ext1O__Format : pLMN_IdentityInfo__ext1O__Type t_Format

val pLMN_IdentityInfo__ext1__check_all_none :
  pLMN_IdentityInfo__ext1O__Type -> bool

val pLMN_IdentityInfo__ext1__Format : pLMN_IdentityInfo__ext1__Type t_Format

type pLMN_IdentityInfo__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))))

val pLMN_IdentityInfo__root_Format_list : pLMN_IdentityInfo__root_Format_Type

type pLMN_IdentityInfo__ext_Format_Type =
  pLMN_IdentityInfo__ext0__Type t_Format * (pLMN_IdentityInfo__ext1__Type
  t_Format * unit t_Format)

val pLMN_IdentityInfo__ext_Format_list : pLMN_IdentityInfo__ext_Format_Type

type pLMN_IdentityInfo__list_type = seq_type * seq_ext_type

val pLMN_IdentityInfo__list_format : pLMN_IdentityInfo__list_type t_Format

val pLMN_IdentityInfo__F1 :
  pLMN_IdentityInfo__Type -> pLMN_IdentityInfo__list_type

val pLMN_IdentityInfo__F2 :
  pLMN_IdentityInfo__list_type -> pLMN_IdentityInfo__Type

val pLMN_IdentityInfo__Format : pLMN_IdentityInfo__Type t_Format

type pLMN_IdentityInfoList__Type = pLMN_IdentityInfo__Type list

val pLMN_IdentityInfoList__Format : pLMN_IdentityInfoList__Type t_Format

type freqBandIndicatorNR__Type = int

val freqBandIndicatorNR__Format : int t_Format

type multiFrequencyBandListNR__Type = freqBandIndicatorNR__Type list

val multiFrequencyBandListNR__Format : multiFrequencyBandListNR__Type t_Format

type controlResourceSetZero__Type = int

val controlResourceSetZero__Format : int t_Format

type searchSpaceZero__Type = int

val searchSpaceZero__Format : int t_Format

type pDCCH_ConfigSIB1__Type = { pDCCH_ConfigSIB1__controlResourceSetZero : 
                                controlResourceSetZero__Type;
                                pDCCH_ConfigSIB1__searchSpaceZero : searchSpaceZero__Type }

val pDCCH_ConfigSIB1__list : seq_elem list

type pDCCH_ConfigSIB1__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val pDCCH_ConfigSIB1__Format_list : pDCCH_ConfigSIB1__Format_Type

val pDCCH_ConfigSIB1__list__Format : seq_type t_Format

val pDCCH_ConfigSIB1__F1 :
  pDCCH_ConfigSIB1__Type ->
  controlResourceSetZero__Type * (searchSpaceZero__Type * unit)

val pDCCH_ConfigSIB1__F2 : seq_type -> pDCCH_ConfigSIB1__Type

val pDCCH_ConfigSIB1__Format : pDCCH_ConfigSIB1__Type t_Format

type cAG_IdentityInfo_r16__cag_Identity_r16__Type = bit_string_fixed

type cAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__Type =
| CAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__true

val cAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__nat__Format :
  int t_Format

val cAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__F1 :
  cAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__Type -> int

val cAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__F2 :
  int -> cAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__Type

type cAG_IdentityInfo_r16__Type = { cAG_IdentityInfo_r16__cag_Identity_r16 : 
                                    cAG_IdentityInfo_r16__cag_Identity_r16__Type;
                                    cAG_IdentityInfo_r16__manualCAGselectionAllowed_r16 : 
                                    cAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__Type
                                    option }

val cAG_IdentityInfo_r16__list : seq_elem list

val cAG_IdentityInfo_r16__cag_Identity_r16__Format :
  cAG_IdentityInfo_r16__cag_Identity_r16__Type t_Format

val cAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__Format :
  cAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__Type t_Format

type cAG_IdentityInfo_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val cAG_IdentityInfo_r16__Format_list : cAG_IdentityInfo_r16__Format_Type

val cAG_IdentityInfo_r16__list__Format : seq_type t_Format

val cAG_IdentityInfo_r16__F1 :
  cAG_IdentityInfo_r16__Type ->
  cAG_IdentityInfo_r16__cag_Identity_r16__Type * (cAG_IdentityInfo_r16__manualCAGselectionAllowed_r16__Type
  option * unit)

val cAG_IdentityInfo_r16__F2 : seq_type -> cAG_IdentityInfo_r16__Type

val cAG_IdentityInfo_r16__Format : cAG_IdentityInfo_r16__Type t_Format

type nID_r16__Type = bit_string_fixed

val nID_r16__Format : nID_r16__Type t_Format

type nPN_Identity_r16__pni_npn_r16__cag_IdentityList_r16__Type =
  cAG_IdentityInfo_r16__Type list

type nPN_Identity_r16__pni_npn_r16__Type = { nPN_Identity_r16__pni_npn_r16__plmn_Identity_r16 : 
                                             pLMN_Identity__Type;
                                             nPN_Identity_r16__pni_npn_r16__cag_IdentityList_r16 : 
                                             nPN_Identity_r16__pni_npn_r16__cag_IdentityList_r16__Type }

val nPN_Identity_r16__pni_npn_r16__list : seq_elem list

type nPN_Identity_r16__snpn_r16__nid_List_r16__Type = nID_r16__Type list

type nPN_Identity_r16__snpn_r16__Type = { nPN_Identity_r16__snpn_r16__plmn_Identity_r16 : 
                                          pLMN_Identity__Type;
                                          nPN_Identity_r16__snpn_r16__nid_List_r16 : 
                                          nPN_Identity_r16__snpn_r16__nid_List_r16__Type }

val nPN_Identity_r16__snpn_r16__list : seq_elem list

type nPN_Identity_r16__Type =
| NPN_Identity_r16__pni_npn_r16 of nPN_Identity_r16__pni_npn_r16__Type
| NPN_Identity_r16__snpn_r16 of nPN_Identity_r16__snpn_r16__Type

val nPN_Identity_r16__pni_npn_r16__cag_IdentityList_r16__Format :
  nPN_Identity_r16__pni_npn_r16__cag_IdentityList_r16__Type t_Format

type nPN_Identity_r16__pni_npn_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val nPN_Identity_r16__pni_npn_r16__Format_list :
  nPN_Identity_r16__pni_npn_r16__Format_Type

val nPN_Identity_r16__pni_npn_r16__list__Format : seq_type t_Format

val nPN_Identity_r16__pni_npn_r16__F1 :
  nPN_Identity_r16__pni_npn_r16__Type ->
  pLMN_Identity__Type * (nPN_Identity_r16__pni_npn_r16__cag_IdentityList_r16__Type * unit)

val nPN_Identity_r16__pni_npn_r16__F2 :
  seq_type -> nPN_Identity_r16__pni_npn_r16__Type

val nPN_Identity_r16__pni_npn_r16__Format :
  nPN_Identity_r16__pni_npn_r16__Type t_Format

val nPN_Identity_r16__snpn_r16__nid_List_r16__Format :
  nPN_Identity_r16__snpn_r16__nid_List_r16__Type t_Format

type nPN_Identity_r16__snpn_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val nPN_Identity_r16__snpn_r16__Format_list :
  nPN_Identity_r16__snpn_r16__Format_Type

val nPN_Identity_r16__snpn_r16__list__Format : seq_type t_Format

val nPN_Identity_r16__snpn_r16__F1 :
  nPN_Identity_r16__snpn_r16__Type ->
  pLMN_Identity__Type * (nPN_Identity_r16__snpn_r16__nid_List_r16__Type * unit)

val nPN_Identity_r16__snpn_r16__F2 :
  seq_type -> nPN_Identity_r16__snpn_r16__Type

val nPN_Identity_r16__snpn_r16__Format :
  nPN_Identity_r16__snpn_r16__Type t_Format

val nPN_Identity_r16__list__Format : (int, __) sigT t_Format

val nPN_Identity_r16__F1 : nPN_Identity_r16__Type -> choice

val nPN_Identity_r16__F2 : choice -> nPN_Identity_r16__Type

val nPN_Identity_r16__Format : nPN_Identity_r16__Type t_Format

type nPN_IdentityInfo_r16__npn_IdentityList_r16__Type =
  nPN_Identity_r16__Type list

type nPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__Type =
| NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__reserved
| NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__notReserved

val nPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__nat__Format :
  int t_Format

val nPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__F1 :
  nPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__Type -> int

val nPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__F2 :
  int -> nPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__Type

type nPN_IdentityInfo_r16__iab_Support_r16__Type =
| NPN_IdentityInfo_r16__iab_Support_r16__true

val nPN_IdentityInfo_r16__iab_Support_r16__nat__Format : int t_Format

val nPN_IdentityInfo_r16__iab_Support_r16__F1 :
  nPN_IdentityInfo_r16__iab_Support_r16__Type -> int

val nPN_IdentityInfo_r16__iab_Support_r16__F2 :
  int -> nPN_IdentityInfo_r16__iab_Support_r16__Type

type nPN_IdentityInfo_r16__ext0O__Type = { nPN_IdentityInfo_r16__ext0O__gNB_ID_Length_r17 : 
                                           int option }

val nPN_IdentityInfo_r16__ext0O__list : seq_elem list

type nPN_IdentityInfo_r16__ext0__Type = nPN_IdentityInfo_r16__ext0O__Type

type nPN_IdentityInfo_r16__Type = { nPN_IdentityInfo_r16__npn_IdentityList_r16 : 
                                    nPN_IdentityInfo_r16__npn_IdentityList_r16__Type;
                                    nPN_IdentityInfo_r16__trackingAreaCode_r16 : 
                                    trackingAreaCode__Type;
                                    nPN_IdentityInfo_r16__ranac_r16 : 
                                    rAN_AreaCode__Type option;
                                    nPN_IdentityInfo_r16__cellIdentity_r16 : 
                                    cellIdentity__Type;
                                    nPN_IdentityInfo_r16__cellReservedForOperatorUse_r16 : 
                                    nPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__Type;
                                    nPN_IdentityInfo_r16__iab_Support_r16 : 
                                    nPN_IdentityInfo_r16__iab_Support_r16__Type
                                    option;
                                    nPN_IdentityInfo_r16__ext0 : nPN_IdentityInfo_r16__ext0__Type
                                                                 option }

val nPN_IdentityInfo_r16__root_list : seq_elem list

val nPN_IdentityInfo_r16__ext_list : typ list

val nPN_IdentityInfo_r16__npn_IdentityList_r16__Format :
  nPN_IdentityInfo_r16__npn_IdentityList_r16__Type t_Format

val nPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__Format :
  nPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__Type t_Format

val nPN_IdentityInfo_r16__iab_Support_r16__Format :
  nPN_IdentityInfo_r16__iab_Support_r16__Type t_Format

val nPN_IdentityInfo_r16__ext0O__gNB_ID_Length_r17__Format : int t_Format

type nPN_IdentityInfo_r16__ext0O__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val nPN_IdentityInfo_r16__ext0O__Format_list :
  nPN_IdentityInfo_r16__ext0O__Format_Type

val nPN_IdentityInfo_r16__ext0O__list__Format : seq_type t_Format

val nPN_IdentityInfo_r16__ext0O__F1 :
  nPN_IdentityInfo_r16__ext0O__Type -> int option * unit

val nPN_IdentityInfo_r16__ext0O__F2 :
  seq_type -> nPN_IdentityInfo_r16__ext0O__Type

val nPN_IdentityInfo_r16__ext0O__Format :
  nPN_IdentityInfo_r16__ext0O__Type t_Format

val nPN_IdentityInfo_r16__ext0__check_all_none :
  nPN_IdentityInfo_r16__ext0O__Type -> bool

val nPN_IdentityInfo_r16__ext0__Format :
  nPN_IdentityInfo_r16__ext0__Type t_Format

type nPN_IdentityInfo_r16__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))))

val nPN_IdentityInfo_r16__root_Format_list :
  nPN_IdentityInfo_r16__root_Format_Type

type nPN_IdentityInfo_r16__ext_Format_Type =
  nPN_IdentityInfo_r16__ext0__Type t_Format * unit t_Format

val nPN_IdentityInfo_r16__ext_Format_list :
  nPN_IdentityInfo_r16__ext_Format_Type

type nPN_IdentityInfo_r16__list_type = seq_type * seq_ext_type

val nPN_IdentityInfo_r16__list_format :
  nPN_IdentityInfo_r16__list_type t_Format

val nPN_IdentityInfo_r16__F1 :
  nPN_IdentityInfo_r16__Type -> nPN_IdentityInfo_r16__list_type

val nPN_IdentityInfo_r16__F2 :
  nPN_IdentityInfo_r16__list_type -> nPN_IdentityInfo_r16__Type

val nPN_IdentityInfo_r16__Format : nPN_IdentityInfo_r16__Type t_Format

type nPN_IdentityInfoList_r16__Type = nPN_IdentityInfo_r16__Type list

val nPN_IdentityInfoList_r16__Format : nPN_IdentityInfoList_r16__Type t_Format

type cGI_InfoNR__noSIB1__Type = { cGI_InfoNR__noSIB1__ssb_SubcarrierOffset : 
                                  int;
                                  cGI_InfoNR__noSIB1__pdcch_ConfigSIB1 : 
                                  pDCCH_ConfigSIB1__Type }

val cGI_InfoNR__noSIB1__list : seq_elem list

type cGI_InfoNR__ext0O__Type = { cGI_InfoNR__ext0O__npn_IdentityInfoList_r16 : 
                                 nPN_IdentityInfoList_r16__Type option }

val cGI_InfoNR__ext0O__list : seq_elem list

type cGI_InfoNR__ext0__Type = cGI_InfoNR__ext0O__Type

type cGI_InfoNR__ext1O__cellReservedForOtherUse_r16__Type =
| CGI_InfoNR__ext1O__cellReservedForOtherUse_r16__true

val cGI_InfoNR__ext1O__cellReservedForOtherUse_r16__nat__Format : int t_Format

val cGI_InfoNR__ext1O__cellReservedForOtherUse_r16__F1 :
  cGI_InfoNR__ext1O__cellReservedForOtherUse_r16__Type -> int

val cGI_InfoNR__ext1O__cellReservedForOtherUse_r16__F2 :
  int -> cGI_InfoNR__ext1O__cellReservedForOtherUse_r16__Type

type cGI_InfoNR__ext1O__Type = { cGI_InfoNR__ext1O__cellReservedForOtherUse_r16 : 
                                 cGI_InfoNR__ext1O__cellReservedForOtherUse_r16__Type
                                 option }

val cGI_InfoNR__ext1O__list : seq_elem list

type cGI_InfoNR__ext1__Type = cGI_InfoNR__ext1O__Type

type cGI_InfoNR__Type = { cGI_InfoNR__plmn_IdentityInfoList : pLMN_IdentityInfoList__Type
                                                              option;
                          cGI_InfoNR__frequencyBandList : multiFrequencyBandListNR__Type
                                                          option;
                          cGI_InfoNR__noSIB1 : cGI_InfoNR__noSIB1__Type option;
                          cGI_InfoNR__ext0 : cGI_InfoNR__ext0__Type option;
                          cGI_InfoNR__ext1 : cGI_InfoNR__ext1__Type option }

val cGI_InfoNR__root_list : seq_elem list

val cGI_InfoNR__ext_list : typ list

val cGI_InfoNR__noSIB1__ssb_SubcarrierOffset__Format : int t_Format

type cGI_InfoNR__noSIB1__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val cGI_InfoNR__noSIB1__Format_list : cGI_InfoNR__noSIB1__Format_Type

val cGI_InfoNR__noSIB1__list__Format : seq_type t_Format

val cGI_InfoNR__noSIB1__F1 :
  cGI_InfoNR__noSIB1__Type -> int * (pDCCH_ConfigSIB1__Type * unit)

val cGI_InfoNR__noSIB1__F2 : seq_type -> cGI_InfoNR__noSIB1__Type

val cGI_InfoNR__noSIB1__Format : cGI_InfoNR__noSIB1__Type t_Format

type cGI_InfoNR__ext0O__Format_Type = seq_elem_to_format * seq_elem_to_format

val cGI_InfoNR__ext0O__Format_list : cGI_InfoNR__ext0O__Format_Type

val cGI_InfoNR__ext0O__list__Format : seq_type t_Format

val cGI_InfoNR__ext0O__F1 :
  cGI_InfoNR__ext0O__Type -> nPN_IdentityInfoList_r16__Type option * unit

val cGI_InfoNR__ext0O__F2 : seq_type -> cGI_InfoNR__ext0O__Type

val cGI_InfoNR__ext0O__Format : cGI_InfoNR__ext0O__Type t_Format

val cGI_InfoNR__ext0__check_all_none : cGI_InfoNR__ext0O__Type -> bool

val cGI_InfoNR__ext0__Format : cGI_InfoNR__ext0__Type t_Format

val cGI_InfoNR__ext1O__cellReservedForOtherUse_r16__Format :
  cGI_InfoNR__ext1O__cellReservedForOtherUse_r16__Type t_Format

type cGI_InfoNR__ext1O__Format_Type = seq_elem_to_format * seq_elem_to_format

val cGI_InfoNR__ext1O__Format_list : cGI_InfoNR__ext1O__Format_Type

val cGI_InfoNR__ext1O__list__Format : seq_type t_Format

val cGI_InfoNR__ext1O__F1 :
  cGI_InfoNR__ext1O__Type ->
  cGI_InfoNR__ext1O__cellReservedForOtherUse_r16__Type option * unit

val cGI_InfoNR__ext1O__F2 : seq_type -> cGI_InfoNR__ext1O__Type

val cGI_InfoNR__ext1O__Format : cGI_InfoNR__ext1O__Type t_Format

val cGI_InfoNR__ext1__check_all_none : cGI_InfoNR__ext1O__Type -> bool

val cGI_InfoNR__ext1__Format : cGI_InfoNR__ext1__Type t_Format

type cGI_InfoNR__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val cGI_InfoNR__root_Format_list : cGI_InfoNR__root_Format_Type

type cGI_InfoNR__ext_Format_Type =
  cGI_InfoNR__ext0__Type t_Format * (cGI_InfoNR__ext1__Type t_Format * unit
  t_Format)

val cGI_InfoNR__ext_Format_list : cGI_InfoNR__ext_Format_Type

type cGI_InfoNR__list_type = seq_type * seq_ext_type

val cGI_InfoNR__list_format : cGI_InfoNR__list_type t_Format

val cGI_InfoNR__F1 : cGI_InfoNR__Type -> cGI_InfoNR__list_type

val cGI_InfoNR__F2 : cGI_InfoNR__list_type -> cGI_InfoNR__Type

val cGI_InfoNR__Format : cGI_InfoNR__Type t_Format

type measTriggerQuantityOffset__Type =
| MeasTriggerQuantityOffset__rsrp of int
| MeasTriggerQuantityOffset__rsrq of int
| MeasTriggerQuantityOffset__sinr of int

val measTriggerQuantityOffset__rsrp__Format : int t_Format

val measTriggerQuantityOffset__rsrq__Format : int t_Format

val measTriggerQuantityOffset__sinr__Format : int t_Format

val measTriggerQuantityOffset__list__Format : (int, __) sigT t_Format

val measTriggerQuantityOffset__F1 : measTriggerQuantityOffset__Type -> choice

val measTriggerQuantityOffset__F2 : choice -> measTriggerQuantityOffset__Type

val measTriggerQuantityOffset__Format :
  measTriggerQuantityOffset__Type t_Format

type hysteresis__Type = int

val hysteresis__Format : int t_Format

type timeToTrigger__Type =
| TimeToTrigger__ms0
| TimeToTrigger__ms40
| TimeToTrigger__ms64
| TimeToTrigger__ms80
| TimeToTrigger__ms100
| TimeToTrigger__ms128
| TimeToTrigger__ms160
| TimeToTrigger__ms256
| TimeToTrigger__ms320
| TimeToTrigger__ms480
| TimeToTrigger__ms512
| TimeToTrigger__ms640
| TimeToTrigger__ms1024
| TimeToTrigger__ms1280
| TimeToTrigger__ms2560
| TimeToTrigger__ms5120

val timeToTrigger__nat__Format : int t_Format

val timeToTrigger__F1 : timeToTrigger__Type -> int

val timeToTrigger__F2 : int -> timeToTrigger__Type

val timeToTrigger__Format : timeToTrigger__Type t_Format

type measTriggerQuantity__Type =
| MeasTriggerQuantity__rsrp of rSRP_Range__Type
| MeasTriggerQuantity__rsrq of rSRQ_Range__Type
| MeasTriggerQuantity__sinr of sINR_Range__Type

val measTriggerQuantity__list__Format : (int, __) sigT t_Format

val measTriggerQuantity__F1 : measTriggerQuantity__Type -> choice

val measTriggerQuantity__F2 : choice -> measTriggerQuantity__Type

val measTriggerQuantity__Format : measTriggerQuantity__Type t_Format

type referenceLocation_r17__Type = octet_string

val referenceLocation_r17__Format : char list t_Format

type hysteresisLocation_r17__Type = int

val hysteresisLocation_r17__Format : int t_Format

type nR_RS_Type__Type =
| NR_RS_Type__ssb
| NR_RS_Type__csi_rs

val nR_RS_Type__nat__Format : int t_Format

val nR_RS_Type__F1 : nR_RS_Type__Type -> int

val nR_RS_Type__F2 : int -> nR_RS_Type__Type

val nR_RS_Type__Format : nR_RS_Type__Type t_Format

type condTriggerConfig_r16__condEventId__root__condEventA3__Type = { condTriggerConfig_r16__condEventId__root__condEventA3__a3_Offset : 
                                                                     measTriggerQuantityOffset__Type;
                                                                     condTriggerConfig_r16__condEventId__root__condEventA3__hysteresis : 
                                                                     hysteresis__Type;
                                                                     condTriggerConfig_r16__condEventId__root__condEventA3__timeToTrigger : 
                                                                     timeToTrigger__Type }

val condTriggerConfig_r16__condEventId__root__condEventA3__list : seq_elem list

type condTriggerConfig_r16__condEventId__root__condEventA5__Type = { condTriggerConfig_r16__condEventId__root__condEventA5__a5_Threshold1 : 
                                                                     measTriggerQuantity__Type;
                                                                     condTriggerConfig_r16__condEventId__root__condEventA5__a5_Threshold2 : 
                                                                     measTriggerQuantity__Type;
                                                                     condTriggerConfig_r16__condEventId__root__condEventA5__hysteresis : 
                                                                     hysteresis__Type;
                                                                     condTriggerConfig_r16__condEventId__root__condEventA5__timeToTrigger : 
                                                                     timeToTrigger__Type }

val condTriggerConfig_r16__condEventId__root__condEventA5__list : seq_elem list

type condTriggerConfig_r16__condEventId__root__Type =
| CondTriggerConfig_r16__condEventId__root__condEventA3 of condTriggerConfig_r16__condEventId__root__condEventA3__Type
| CondTriggerConfig_r16__condEventId__root__condEventA5 of condTriggerConfig_r16__condEventId__root__condEventA5__Type

type condTriggerConfig_r16__condEventId__ext__condEventA4_r17__Type = { 
condTriggerConfig_r16__condEventId__ext__condEventA4_r17__a4_Threshold_r17 : 
measTriggerQuantity__Type;
condTriggerConfig_r16__condEventId__ext__condEventA4_r17__hysteresis_r17 : 
hysteresis__Type;
condTriggerConfig_r16__condEventId__ext__condEventA4_r17__timeToTrigger_r17 : 
timeToTrigger__Type }

val condTriggerConfig_r16__condEventId__ext__condEventA4_r17__list :
  seq_elem list

type condTriggerConfig_r16__condEventId__ext__condEventD1_r17__Type = { 
condTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference1_r17 : 
int;
condTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference2_r17 : 
int;
condTriggerConfig_r16__condEventId__ext__condEventD1_r17__referenceLocation1_r17 : 
referenceLocation_r17__Type;
condTriggerConfig_r16__condEventId__ext__condEventD1_r17__referenceLocation2_r17 : 
referenceLocation_r17__Type;
condTriggerConfig_r16__condEventId__ext__condEventD1_r17__hysteresisLocation_r17 : 
hysteresisLocation_r17__Type;
condTriggerConfig_r16__condEventId__ext__condEventD1_r17__timeToTrigger_r17 : 
timeToTrigger__Type }

val condTriggerConfig_r16__condEventId__ext__condEventD1_r17__list :
  seq_elem list

type condTriggerConfig_r16__condEventId__ext__condEventT1_r17__Type = { 
condTriggerConfig_r16__condEventId__ext__condEventT1_r17__t1_Threshold_r17 : 
int;
condTriggerConfig_r16__condEventId__ext__condEventT1_r17__duration_r17 : 
int }

val condTriggerConfig_r16__condEventId__ext__condEventT1_r17__list :
  seq_elem list

type condTriggerConfig_r16__condEventId__ext__Type =
| CondTriggerConfig_r16__condEventId__ext__condEventA4_r17 of condTriggerConfig_r16__condEventId__ext__condEventA4_r17__Type
| CondTriggerConfig_r16__condEventId__ext__condEventD1_r17 of condTriggerConfig_r16__condEventId__ext__condEventD1_r17__Type
| CondTriggerConfig_r16__condEventId__ext__condEventT1_r17 of condTriggerConfig_r16__condEventId__ext__condEventT1_r17__Type

type condTriggerConfig_r16__condEventId__Type =
  (condTriggerConfig_r16__condEventId__root__Type,
  condTriggerConfig_r16__condEventId__ext__Type) sum

type condTriggerConfig_r16__Type = { condTriggerConfig_r16__condEventId : 
                                     condTriggerConfig_r16__condEventId__Type;
                                     condTriggerConfig_r16__rsType_r16 : 
                                     nR_RS_Type__Type }

val condTriggerConfig_r16__root_list : seq_elem list

val condTriggerConfig_r16__ext_list : typ list

type condTriggerConfig_r16__condEventId__root__condEventA3__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val condTriggerConfig_r16__condEventId__root__condEventA3__Format_list :
  condTriggerConfig_r16__condEventId__root__condEventA3__Format_Type

val condTriggerConfig_r16__condEventId__root__condEventA3__list__Format :
  seq_type t_Format

val condTriggerConfig_r16__condEventId__root__condEventA3__F1 :
  condTriggerConfig_r16__condEventId__root__condEventA3__Type ->
  measTriggerQuantityOffset__Type * (hysteresis__Type * (timeToTrigger__Type * unit))

val condTriggerConfig_r16__condEventId__root__condEventA3__F2 :
  seq_type -> condTriggerConfig_r16__condEventId__root__condEventA3__Type

val condTriggerConfig_r16__condEventId__root__condEventA3__Format :
  condTriggerConfig_r16__condEventId__root__condEventA3__Type t_Format

type condTriggerConfig_r16__condEventId__root__condEventA5__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

val condTriggerConfig_r16__condEventId__root__condEventA5__Format_list :
  condTriggerConfig_r16__condEventId__root__condEventA5__Format_Type

val condTriggerConfig_r16__condEventId__root__condEventA5__list__Format :
  seq_type t_Format

val condTriggerConfig_r16__condEventId__root__condEventA5__F1 :
  condTriggerConfig_r16__condEventId__root__condEventA5__Type ->
  measTriggerQuantity__Type * (measTriggerQuantity__Type * (hysteresis__Type * (timeToTrigger__Type * unit)))

val condTriggerConfig_r16__condEventId__root__condEventA5__F2 :
  seq_type -> condTriggerConfig_r16__condEventId__root__condEventA5__Type

val condTriggerConfig_r16__condEventId__root__condEventA5__Format :
  condTriggerConfig_r16__condEventId__root__condEventA5__Type t_Format

val condTriggerConfig_r16__condEventId__root__list__Format :
  (int, __) sigT t_Format

val condTriggerConfig_r16__condEventId__root__F1 :
  condTriggerConfig_r16__condEventId__root__Type -> choice

val condTriggerConfig_r16__condEventId__root__F2 :
  choice -> condTriggerConfig_r16__condEventId__root__Type

val condTriggerConfig_r16__condEventId__root__Format :
  condTriggerConfig_r16__condEventId__root__Type t_Format

type condTriggerConfig_r16__condEventId__ext__condEventA4_r17__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val condTriggerConfig_r16__condEventId__ext__condEventA4_r17__Format_list :
  condTriggerConfig_r16__condEventId__ext__condEventA4_r17__Format_Type

val condTriggerConfig_r16__condEventId__ext__condEventA4_r17__list__Format :
  seq_type t_Format

val condTriggerConfig_r16__condEventId__ext__condEventA4_r17__F1 :
  condTriggerConfig_r16__condEventId__ext__condEventA4_r17__Type ->
  measTriggerQuantity__Type * (hysteresis__Type * (timeToTrigger__Type * unit))

val condTriggerConfig_r16__condEventId__ext__condEventA4_r17__F2 :
  seq_type -> condTriggerConfig_r16__condEventId__ext__condEventA4_r17__Type

val condTriggerConfig_r16__condEventId__ext__condEventA4_r17__Format :
  condTriggerConfig_r16__condEventId__ext__condEventA4_r17__Type t_Format

val condTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference1_r17__Format :
  int t_Format

val condTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference2_r17__Format :
  int t_Format

type condTriggerConfig_r16__condEventId__ext__condEventD1_r17__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))))

val condTriggerConfig_r16__condEventId__ext__condEventD1_r17__Format_list :
  condTriggerConfig_r16__condEventId__ext__condEventD1_r17__Format_Type

val condTriggerConfig_r16__condEventId__ext__condEventD1_r17__list__Format :
  seq_type t_Format

val condTriggerConfig_r16__condEventId__ext__condEventD1_r17__F1 :
  condTriggerConfig_r16__condEventId__ext__condEventD1_r17__Type ->
  int * (int * (referenceLocation_r17__Type * (referenceLocation_r17__Type * (hysteresisLocation_r17__Type * (timeToTrigger__Type * unit)))))

val condTriggerConfig_r16__condEventId__ext__condEventD1_r17__F2 :
  seq_type -> condTriggerConfig_r16__condEventId__ext__condEventD1_r17__Type

val condTriggerConfig_r16__condEventId__ext__condEventD1_r17__Format :
  condTriggerConfig_r16__condEventId__ext__condEventD1_r17__Type t_Format

val condTriggerConfig_r16__condEventId__ext__condEventT1_r17__t1_Threshold_r17__Format :
  int t_Format

val condTriggerConfig_r16__condEventId__ext__condEventT1_r17__duration_r17__Format :
  int t_Format

type condTriggerConfig_r16__condEventId__ext__condEventT1_r17__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val condTriggerConfig_r16__condEventId__ext__condEventT1_r17__Format_list :
  condTriggerConfig_r16__condEventId__ext__condEventT1_r17__Format_Type

val condTriggerConfig_r16__condEventId__ext__condEventT1_r17__list__Format :
  seq_type t_Format

val condTriggerConfig_r16__condEventId__ext__condEventT1_r17__F1 :
  condTriggerConfig_r16__condEventId__ext__condEventT1_r17__Type ->
  int * (int * unit)

val condTriggerConfig_r16__condEventId__ext__condEventT1_r17__F2 :
  seq_type -> condTriggerConfig_r16__condEventId__ext__condEventT1_r17__Type

val condTriggerConfig_r16__condEventId__ext__condEventT1_r17__Format :
  condTriggerConfig_r16__condEventId__ext__condEventT1_r17__Type t_Format

val condTriggerConfig_r16__condEventId__ext__list__Format :
  (int, __) sigT t_Format

val condTriggerConfig_r16__condEventId__ext__F1 :
  condTriggerConfig_r16__condEventId__ext__Type -> choice

val condTriggerConfig_r16__condEventId__ext__F2 :
  choice -> condTriggerConfig_r16__condEventId__ext__Type

val condTriggerConfig_r16__condEventId__ext__Format :
  condTriggerConfig_r16__condEventId__ext__Type t_Format

val condTriggerConfig_r16__condEventId__Format :
  condTriggerConfig_r16__condEventId__Type t_Format

type condTriggerConfig_r16__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val condTriggerConfig_r16__root_Format_list :
  condTriggerConfig_r16__root_Format_Type

type condTriggerConfig_r16__ext_Format_Type = unit t_Format

val condTriggerConfig_r16__ext_Format_list :
  condTriggerConfig_r16__ext_Format_Type

type condTriggerConfig_r16__list_type = seq_type * seq_ext_type

val condTriggerConfig_r16__list_format :
  condTriggerConfig_r16__list_type t_Format

val condTriggerConfig_r16__F1 :
  condTriggerConfig_r16__Type -> condTriggerConfig_r16__list_type

val condTriggerConfig_r16__F2 :
  condTriggerConfig_r16__list_type -> condTriggerConfig_r16__Type

val condTriggerConfig_r16__Format : condTriggerConfig_r16__Type t_Format

type timeBetweenEvent_r17__Type = int

val timeBetweenEvent_r17__Format : int t_Format

type measResultNR__measResult__cellResults__Type = { measResultNR__measResult__cellResults__resultsSSB_Cell : 
                                                     measQuantityResults__Type
                                                     option;
                                                     measResultNR__measResult__cellResults__resultsCSI_RS_Cell : 
                                                     measQuantityResults__Type
                                                     option }

val measResultNR__measResult__cellResults__list : seq_elem list

type measResultNR__measResult__rsIndexResults__Type = { measResultNR__measResult__rsIndexResults__resultsSSB_Indexes : 
                                                        resultsPerSSB_IndexList__Type
                                                        option;
                                                        measResultNR__measResult__rsIndexResults__resultsCSI_RS_Indexes : 
                                                        resultsPerCSI_RS_IndexList__Type
                                                        option }

val measResultNR__measResult__rsIndexResults__list : seq_elem list

type measResultNR__measResult__Type = { measResultNR__measResult__cellResults : 
                                        measResultNR__measResult__cellResults__Type;
                                        measResultNR__measResult__rsIndexResults : 
                                        measResultNR__measResult__rsIndexResults__Type
                                        option }

val measResultNR__measResult__list : seq_elem list

type measResultNR__ext0O__Type = { measResultNR__ext0O__cgi_Info : cGI_InfoNR__Type
                                                                   option }

val measResultNR__ext0O__list : seq_elem list

type measResultNR__ext0__Type = measResultNR__ext0O__Type

type measResultNR__ext1O__choCandidate_r17__Type =
| MeasResultNR__ext1O__choCandidate_r17__true

val measResultNR__ext1O__choCandidate_r17__nat__Format : int t_Format

val measResultNR__ext1O__choCandidate_r17__F1 :
  measResultNR__ext1O__choCandidate_r17__Type -> int

val measResultNR__ext1O__choCandidate_r17__F2 :
  int -> measResultNR__ext1O__choCandidate_r17__Type

type measResultNR__ext1O__choConfig_r17__Type =
  condTriggerConfig_r16__Type list

type measResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__Type =
| MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__condFirstEvent
| MeasResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__condSecondEvent

val measResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__nat__Format :
  int t_Format

val measResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__F1 :
  measResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__Type -> int

val measResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__F2 :
  int -> measResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__Type

type measResultNR__ext1O__triggeredEvent_r17__Type = { measResultNR__ext1O__triggeredEvent_r17__timeBetweenEvents_r17 : 
                                                       timeBetweenEvent_r17__Type
                                                       option;
                                                       measResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent : 
                                                       measResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__Type
                                                       option }

val measResultNR__ext1O__triggeredEvent_r17__list : seq_elem list

type measResultNR__ext1O__Type = { measResultNR__ext1O__choCandidate_r17 : 
                                   measResultNR__ext1O__choCandidate_r17__Type
                                   option;
                                   measResultNR__ext1O__choConfig_r17 : 
                                   measResultNR__ext1O__choConfig_r17__Type
                                   option;
                                   measResultNR__ext1O__triggeredEvent_r17 : 
                                   measResultNR__ext1O__triggeredEvent_r17__Type
                                   option }

val measResultNR__ext1O__list : seq_elem list

type measResultNR__ext1__Type = measResultNR__ext1O__Type

type measResultNR__Type = { measResultNR__physCellId : physCellId__Type option;
                            measResultNR__measResult : measResultNR__measResult__Type;
                            measResultNR__ext0 : measResultNR__ext0__Type
                                                 option;
                            measResultNR__ext1 : measResultNR__ext1__Type
                                                 option }

val measResultNR__root_list : seq_elem list

val measResultNR__ext_list : typ list

type measResultNR__measResult__cellResults__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val measResultNR__measResult__cellResults__Format_list :
  measResultNR__measResult__cellResults__Format_Type

val measResultNR__measResult__cellResults__list__Format : seq_type t_Format

val measResultNR__measResult__cellResults__F1 :
  measResultNR__measResult__cellResults__Type -> measQuantityResults__Type
  option * (measQuantityResults__Type option * unit)

val measResultNR__measResult__cellResults__F2 :
  seq_type -> measResultNR__measResult__cellResults__Type

val measResultNR__measResult__cellResults__Format :
  measResultNR__measResult__cellResults__Type t_Format

type measResultNR__measResult__rsIndexResults__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val measResultNR__measResult__rsIndexResults__Format_list :
  measResultNR__measResult__rsIndexResults__Format_Type

val measResultNR__measResult__rsIndexResults__list__Format : seq_type t_Format

val measResultNR__measResult__rsIndexResults__F1 :
  measResultNR__measResult__rsIndexResults__Type ->
  resultsPerSSB_IndexList__Type option * (resultsPerCSI_RS_IndexList__Type
  option * unit)

val measResultNR__measResult__rsIndexResults__F2 :
  seq_type -> measResultNR__measResult__rsIndexResults__Type

val measResultNR__measResult__rsIndexResults__Format :
  measResultNR__measResult__rsIndexResults__Type t_Format

type measResultNR__measResult__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val measResultNR__measResult__Format_list :
  measResultNR__measResult__Format_Type

val measResultNR__measResult__list__Format : seq_type t_Format

val measResultNR__measResult__F1 :
  measResultNR__measResult__Type ->
  measResultNR__measResult__cellResults__Type * (measResultNR__measResult__rsIndexResults__Type
  option * unit)

val measResultNR__measResult__F2 : seq_type -> measResultNR__measResult__Type

val measResultNR__measResult__Format : measResultNR__measResult__Type t_Format

type measResultNR__ext0O__Format_Type = seq_elem_to_format * seq_elem_to_format

val measResultNR__ext0O__Format_list : measResultNR__ext0O__Format_Type

val measResultNR__ext0O__list__Format : seq_type t_Format

val measResultNR__ext0O__F1 :
  measResultNR__ext0O__Type -> cGI_InfoNR__Type option * unit

val measResultNR__ext0O__F2 : seq_type -> measResultNR__ext0O__Type

val measResultNR__ext0O__Format : measResultNR__ext0O__Type t_Format

val measResultNR__ext0__check_all_none : measResultNR__ext0O__Type -> bool

val measResultNR__ext0__Format : measResultNR__ext0__Type t_Format

val measResultNR__ext1O__choCandidate_r17__Format :
  measResultNR__ext1O__choCandidate_r17__Type t_Format

val measResultNR__ext1O__choConfig_r17__Format :
  measResultNR__ext1O__choConfig_r17__Type t_Format

val measResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__Format :
  measResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__Type t_Format

type measResultNR__ext1O__triggeredEvent_r17__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val measResultNR__ext1O__triggeredEvent_r17__Format_list :
  measResultNR__ext1O__triggeredEvent_r17__Format_Type

val measResultNR__ext1O__triggeredEvent_r17__list__Format : seq_type t_Format

val measResultNR__ext1O__triggeredEvent_r17__F1 :
  measResultNR__ext1O__triggeredEvent_r17__Type -> timeBetweenEvent_r17__Type
  option * (measResultNR__ext1O__triggeredEvent_r17__firstTriggeredEvent__Type
  option * unit)

val measResultNR__ext1O__triggeredEvent_r17__F2 :
  seq_type -> measResultNR__ext1O__triggeredEvent_r17__Type

val measResultNR__ext1O__triggeredEvent_r17__Format :
  measResultNR__ext1O__triggeredEvent_r17__Type t_Format

type measResultNR__ext1O__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val measResultNR__ext1O__Format_list : measResultNR__ext1O__Format_Type

val measResultNR__ext1O__list__Format : seq_type t_Format

val measResultNR__ext1O__F1 :
  measResultNR__ext1O__Type -> measResultNR__ext1O__choCandidate_r17__Type
  option * (measResultNR__ext1O__choConfig_r17__Type
  option * (measResultNR__ext1O__triggeredEvent_r17__Type option * unit))

val measResultNR__ext1O__F2 : seq_type -> measResultNR__ext1O__Type

val measResultNR__ext1O__Format : measResultNR__ext1O__Type t_Format

val measResultNR__ext1__check_all_none : measResultNR__ext1O__Type -> bool

val measResultNR__ext1__Format : measResultNR__ext1__Type t_Format

type measResultNR__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val measResultNR__root_Format_list : measResultNR__root_Format_Type

type measResultNR__ext_Format_Type =
  measResultNR__ext0__Type t_Format * (measResultNR__ext1__Type
  t_Format * unit t_Format)

val measResultNR__ext_Format_list : measResultNR__ext_Format_Type

type measResultNR__list_type = seq_type * seq_ext_type

val measResultNR__list_format : measResultNR__list_type t_Format

val measResultNR__F1 : measResultNR__Type -> measResultNR__list_type

val measResultNR__F2 : measResultNR__list_type -> measResultNR__Type

val measResultNR__Format : measResultNR__Type t_Format

type measResultServMO__Type = { measResultServMO__servCellId : servCellIndex__Type;
                                measResultServMO__measResultServingCell : 
                                measResultNR__Type;
                                measResultServMO__measResultBestNeighCell : 
                                measResultNR__Type option }

val measResultServMO__root_list : seq_elem list

val measResultServMO__ext_list : typ list

type measResultServMO__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val measResultServMO__root_Format_list : measResultServMO__root_Format_Type

type measResultServMO__ext_Format_Type = unit t_Format

val measResultServMO__ext_Format_list : measResultServMO__ext_Format_Type

type measResultServMO__list_type = seq_type * seq_ext_type

val measResultServMO__list_format : measResultServMO__list_type t_Format

val measResultServMO__F1 :
  measResultServMO__Type -> measResultServMO__list_type

val measResultServMO__F2 :
  measResultServMO__list_type -> measResultServMO__Type

val measResultServMO__Format : measResultServMO__Type t_Format

type measResultServMOList__Type = measResultServMO__Type list

val measResultServMOList__Format : measResultServMOList__Type t_Format

type measResultListNR__Type = measResultNR__Type list

val measResultListNR__Format : measResultListNR__Type t_Format

type rSRP_RangeEUTRA__Type = int

val rSRP_RangeEUTRA__Format : int t_Format

type rSRQ_RangeEUTRA__Type = int

val rSRQ_RangeEUTRA__Format : int t_Format

type sINR_RangeEUTRA__Type = int

val sINR_RangeEUTRA__Format : int t_Format

type measQuantityResultsEUTRA__Type = { measQuantityResultsEUTRA__rsrp : 
                                        rSRP_RangeEUTRA__Type option;
                                        measQuantityResultsEUTRA__rsrq : 
                                        rSRQ_RangeEUTRA__Type option;
                                        measQuantityResultsEUTRA__sinr : 
                                        sINR_RangeEUTRA__Type option }

val measQuantityResultsEUTRA__list : seq_elem list

type measQuantityResultsEUTRA__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val measQuantityResultsEUTRA__Format_list :
  measQuantityResultsEUTRA__Format_Type

val measQuantityResultsEUTRA__list__Format : seq_type t_Format

val measQuantityResultsEUTRA__F1 :
  measQuantityResultsEUTRA__Type -> rSRP_RangeEUTRA__Type
  option * (rSRQ_RangeEUTRA__Type option * (sINR_RangeEUTRA__Type
  option * unit))

val measQuantityResultsEUTRA__F2 : seq_type -> measQuantityResultsEUTRA__Type

val measQuantityResultsEUTRA__Format : measQuantityResultsEUTRA__Type t_Format

type pLMN_IdentityList_EUTRA_EPC__Type = pLMN_Identity__Type list

val pLMN_IdentityList_EUTRA_EPC__Format :
  pLMN_IdentityList_EUTRA_EPC__Type t_Format

type cellAccessRelatedInfo_EUTRA_EPC__trackingAreaCode_eutra_epc__Type =
  bit_string_fixed

type cellAccessRelatedInfo_EUTRA_EPC__cellIdentity_eutra_epc__Type =
  bit_string_fixed

type cellAccessRelatedInfo_EUTRA_EPC__Type = { cellAccessRelatedInfo_EUTRA_EPC__plmn_IdentityList_eutra_epc : 
                                               pLMN_IdentityList_EUTRA_EPC__Type;
                                               cellAccessRelatedInfo_EUTRA_EPC__trackingAreaCode_eutra_epc : 
                                               cellAccessRelatedInfo_EUTRA_EPC__trackingAreaCode_eutra_epc__Type;
                                               cellAccessRelatedInfo_EUTRA_EPC__cellIdentity_eutra_epc : 
                                               cellAccessRelatedInfo_EUTRA_EPC__cellIdentity_eutra_epc__Type }

val cellAccessRelatedInfo_EUTRA_EPC__list : seq_elem list

val cellAccessRelatedInfo_EUTRA_EPC__trackingAreaCode_eutra_epc__Format :
  cellAccessRelatedInfo_EUTRA_EPC__trackingAreaCode_eutra_epc__Type t_Format

val cellAccessRelatedInfo_EUTRA_EPC__cellIdentity_eutra_epc__Format :
  cellAccessRelatedInfo_EUTRA_EPC__cellIdentity_eutra_epc__Type t_Format

type cellAccessRelatedInfo_EUTRA_EPC__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val cellAccessRelatedInfo_EUTRA_EPC__Format_list :
  cellAccessRelatedInfo_EUTRA_EPC__Format_Type

val cellAccessRelatedInfo_EUTRA_EPC__list__Format : seq_type t_Format

val cellAccessRelatedInfo_EUTRA_EPC__F1 :
  cellAccessRelatedInfo_EUTRA_EPC__Type ->
  pLMN_IdentityList_EUTRA_EPC__Type * (cellAccessRelatedInfo_EUTRA_EPC__trackingAreaCode_eutra_epc__Type * (cellAccessRelatedInfo_EUTRA_EPC__cellIdentity_eutra_epc__Type * unit))

val cellAccessRelatedInfo_EUTRA_EPC__F2 :
  seq_type -> cellAccessRelatedInfo_EUTRA_EPC__Type

val cellAccessRelatedInfo_EUTRA_EPC__Format :
  cellAccessRelatedInfo_EUTRA_EPC__Type t_Format

type pLMN_Identity_EUTRA_5GC__Type =
| PLMN_Identity_EUTRA_5GC__plmn_Identity_EUTRA_5GC of pLMN_Identity__Type
| PLMN_Identity_EUTRA_5GC__plmn_index of int

val pLMN_Identity_EUTRA_5GC__plmn_index__Format : int t_Format

val pLMN_Identity_EUTRA_5GC__list__Format : (int, __) sigT t_Format

val pLMN_Identity_EUTRA_5GC__F1 : pLMN_Identity_EUTRA_5GC__Type -> choice

val pLMN_Identity_EUTRA_5GC__F2 : choice -> pLMN_Identity_EUTRA_5GC__Type

val pLMN_Identity_EUTRA_5GC__Format : pLMN_Identity_EUTRA_5GC__Type t_Format

type pLMN_IdentityList_EUTRA_5GC__Type = pLMN_Identity_EUTRA_5GC__Type list

val pLMN_IdentityList_EUTRA_5GC__Format :
  pLMN_IdentityList_EUTRA_5GC__Type t_Format

type cellIdentity_EUTRA_5GC__cellIdentity_EUTRA__Type = bit_string_fixed

type cellIdentity_EUTRA_5GC__Type =
| CellIdentity_EUTRA_5GC__cellIdentity_EUTRA of cellIdentity_EUTRA_5GC__cellIdentity_EUTRA__Type
| CellIdentity_EUTRA_5GC__cellId_index of int

val cellIdentity_EUTRA_5GC__cellIdentity_EUTRA__Format :
  cellIdentity_EUTRA_5GC__cellIdentity_EUTRA__Type t_Format

val cellIdentity_EUTRA_5GC__cellId_index__Format : int t_Format

val cellIdentity_EUTRA_5GC__list__Format : (int, __) sigT t_Format

val cellIdentity_EUTRA_5GC__F1 : cellIdentity_EUTRA_5GC__Type -> choice

val cellIdentity_EUTRA_5GC__F2 : choice -> cellIdentity_EUTRA_5GC__Type

val cellIdentity_EUTRA_5GC__Format : cellIdentity_EUTRA_5GC__Type t_Format

type cellAccessRelatedInfo_EUTRA_5GC__Type = { cellAccessRelatedInfo_EUTRA_5GC__plmn_IdentityList_eutra_5gc : 
                                               pLMN_IdentityList_EUTRA_5GC__Type;
                                               cellAccessRelatedInfo_EUTRA_5GC__trackingAreaCode_eutra_5gc : 
                                               trackingAreaCode__Type;
                                               cellAccessRelatedInfo_EUTRA_5GC__ranac_5gc : 
                                               rAN_AreaCode__Type option;
                                               cellAccessRelatedInfo_EUTRA_5GC__cellIdentity_eutra_5gc : 
                                               cellIdentity_EUTRA_5GC__Type }

val cellAccessRelatedInfo_EUTRA_5GC__list : seq_elem list

type cellAccessRelatedInfo_EUTRA_5GC__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

val cellAccessRelatedInfo_EUTRA_5GC__Format_list :
  cellAccessRelatedInfo_EUTRA_5GC__Format_Type

val cellAccessRelatedInfo_EUTRA_5GC__list__Format : seq_type t_Format

val cellAccessRelatedInfo_EUTRA_5GC__F1 :
  cellAccessRelatedInfo_EUTRA_5GC__Type ->
  pLMN_IdentityList_EUTRA_5GC__Type * (trackingAreaCode__Type * (rAN_AreaCode__Type
  option * (cellIdentity_EUTRA_5GC__Type * unit)))

val cellAccessRelatedInfo_EUTRA_5GC__F2 :
  seq_type -> cellAccessRelatedInfo_EUTRA_5GC__Type

val cellAccessRelatedInfo_EUTRA_5GC__Format :
  cellAccessRelatedInfo_EUTRA_5GC__Type t_Format

type freqBandIndicatorEUTRA__Type = int

val freqBandIndicatorEUTRA__Format : int t_Format

type multiBandInfoListEUTRA__Type = freqBandIndicatorEUTRA__Type list

val multiBandInfoListEUTRA__Format : multiBandInfoListEUTRA__Type t_Format

type cGI_InfoEUTRA__cgi_info_EPC__cgi_info_EPC_list__Type =
  cellAccessRelatedInfo_EUTRA_EPC__Type list

type cGI_InfoEUTRA__cgi_info_EPC__Type = { cGI_InfoEUTRA__cgi_info_EPC__cgi_info_EPC_legacy : 
                                           cellAccessRelatedInfo_EUTRA_EPC__Type;
                                           cGI_InfoEUTRA__cgi_info_EPC__cgi_info_EPC_list : 
                                           cGI_InfoEUTRA__cgi_info_EPC__cgi_info_EPC_list__Type
                                           option }

val cGI_InfoEUTRA__cgi_info_EPC__list : seq_elem list

type cGI_InfoEUTRA__cgi_info_5GC__Type =
  cellAccessRelatedInfo_EUTRA_5GC__Type list

type cGI_InfoEUTRA__freqBandIndicatorPriority__Type =
| CGI_InfoEUTRA__freqBandIndicatorPriority__true

val cGI_InfoEUTRA__freqBandIndicatorPriority__nat__Format : int t_Format

val cGI_InfoEUTRA__freqBandIndicatorPriority__F1 :
  cGI_InfoEUTRA__freqBandIndicatorPriority__Type -> int

val cGI_InfoEUTRA__freqBandIndicatorPriority__F2 :
  int -> cGI_InfoEUTRA__freqBandIndicatorPriority__Type

type cGI_InfoEUTRA__Type = { cGI_InfoEUTRA__cgi_info_EPC : cGI_InfoEUTRA__cgi_info_EPC__Type
                                                           option;
                             cGI_InfoEUTRA__cgi_info_5GC : cGI_InfoEUTRA__cgi_info_5GC__Type
                                                           option;
                             cGI_InfoEUTRA__freqBandIndicator : freqBandIndicatorEUTRA__Type;
                             cGI_InfoEUTRA__multiBandInfoList : multiBandInfoListEUTRA__Type
                                                                option;
                             cGI_InfoEUTRA__freqBandIndicatorPriority : 
                             cGI_InfoEUTRA__freqBandIndicatorPriority__Type
                             option }

val cGI_InfoEUTRA__list : seq_elem list

val cGI_InfoEUTRA__cgi_info_EPC__cgi_info_EPC_list__Format :
  cGI_InfoEUTRA__cgi_info_EPC__cgi_info_EPC_list__Type t_Format

type cGI_InfoEUTRA__cgi_info_EPC__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val cGI_InfoEUTRA__cgi_info_EPC__Format_list :
  cGI_InfoEUTRA__cgi_info_EPC__Format_Type

val cGI_InfoEUTRA__cgi_info_EPC__list__Format : seq_type t_Format

val cGI_InfoEUTRA__cgi_info_EPC__F1 :
  cGI_InfoEUTRA__cgi_info_EPC__Type ->
  cellAccessRelatedInfo_EUTRA_EPC__Type * (cGI_InfoEUTRA__cgi_info_EPC__cgi_info_EPC_list__Type
  option * unit)

val cGI_InfoEUTRA__cgi_info_EPC__F2 :
  seq_type -> cGI_InfoEUTRA__cgi_info_EPC__Type

val cGI_InfoEUTRA__cgi_info_EPC__Format :
  cGI_InfoEUTRA__cgi_info_EPC__Type t_Format

val cGI_InfoEUTRA__cgi_info_5GC__Format :
  cGI_InfoEUTRA__cgi_info_5GC__Type t_Format

val cGI_InfoEUTRA__freqBandIndicatorPriority__Format :
  cGI_InfoEUTRA__freqBandIndicatorPriority__Type t_Format

type cGI_InfoEUTRA__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))))

val cGI_InfoEUTRA__Format_list : cGI_InfoEUTRA__Format_Type

val cGI_InfoEUTRA__list__Format : seq_type t_Format

val cGI_InfoEUTRA__F1 :
  cGI_InfoEUTRA__Type -> cGI_InfoEUTRA__cgi_info_EPC__Type
  option * (cGI_InfoEUTRA__cgi_info_5GC__Type
  option * (freqBandIndicatorEUTRA__Type * (multiBandInfoListEUTRA__Type
  option * (cGI_InfoEUTRA__freqBandIndicatorPriority__Type option * unit))))

val cGI_InfoEUTRA__F2 : seq_type -> cGI_InfoEUTRA__Type

val cGI_InfoEUTRA__Format : cGI_InfoEUTRA__Type t_Format

type measResultEUTRA__Type = { measResultEUTRA__eutra_PhysCellId : physCellId__Type;
                               measResultEUTRA__measResult : measQuantityResultsEUTRA__Type;
                               measResultEUTRA__cgi_Info : cGI_InfoEUTRA__Type
                                                           option }

val measResultEUTRA__root_list : seq_elem list

val measResultEUTRA__ext_list : typ list

type measResultEUTRA__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val measResultEUTRA__root_Format_list : measResultEUTRA__root_Format_Type

type measResultEUTRA__ext_Format_Type = unit t_Format

val measResultEUTRA__ext_Format_list : measResultEUTRA__ext_Format_Type

type measResultEUTRA__list_type = seq_type * seq_ext_type

val measResultEUTRA__list_format : measResultEUTRA__list_type t_Format

val measResultEUTRA__F1 : measResultEUTRA__Type -> measResultEUTRA__list_type

val measResultEUTRA__F2 : measResultEUTRA__list_type -> measResultEUTRA__Type

val measResultEUTRA__Format : measResultEUTRA__Type t_Format

type measResultListEUTRA__Type = measResultEUTRA__Type list

val measResultListEUTRA__Format : measResultListEUTRA__Type t_Format

type physCellIdUTRA_FDD_r16__Type = int

val physCellIdUTRA_FDD_r16__Format : int t_Format

type measResultUTRA_FDD_r16__measResult_r16__Type = { measResultUTRA_FDD_r16__measResult_r16__utra_FDD_RSCP_r16 : 
                                                      int option;
                                                      measResultUTRA_FDD_r16__measResult_r16__utra_FDD_EcN0_r16 : 
                                                      int option }

val measResultUTRA_FDD_r16__measResult_r16__list : seq_elem list

type measResultUTRA_FDD_r16__Type = { measResultUTRA_FDD_r16__physCellId_r16 : 
                                      physCellIdUTRA_FDD_r16__Type;
                                      measResultUTRA_FDD_r16__measResult_r16 : 
                                      measResultUTRA_FDD_r16__measResult_r16__Type }

val measResultUTRA_FDD_r16__list : seq_elem list

val measResultUTRA_FDD_r16__measResult_r16__utra_FDD_RSCP_r16__Format :
  int t_Format

val measResultUTRA_FDD_r16__measResult_r16__utra_FDD_EcN0_r16__Format :
  int t_Format

type measResultUTRA_FDD_r16__measResult_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val measResultUTRA_FDD_r16__measResult_r16__Format_list :
  measResultUTRA_FDD_r16__measResult_r16__Format_Type

val measResultUTRA_FDD_r16__measResult_r16__list__Format : seq_type t_Format

val measResultUTRA_FDD_r16__measResult_r16__F1 :
  measResultUTRA_FDD_r16__measResult_r16__Type -> int option * (int
  option * unit)

val measResultUTRA_FDD_r16__measResult_r16__F2 :
  seq_type -> measResultUTRA_FDD_r16__measResult_r16__Type

val measResultUTRA_FDD_r16__measResult_r16__Format :
  measResultUTRA_FDD_r16__measResult_r16__Type t_Format

type measResultUTRA_FDD_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val measResultUTRA_FDD_r16__Format_list : measResultUTRA_FDD_r16__Format_Type

val measResultUTRA_FDD_r16__list__Format : seq_type t_Format

val measResultUTRA_FDD_r16__F1 :
  measResultUTRA_FDD_r16__Type ->
  physCellIdUTRA_FDD_r16__Type * (measResultUTRA_FDD_r16__measResult_r16__Type * unit)

val measResultUTRA_FDD_r16__F2 : seq_type -> measResultUTRA_FDD_r16__Type

val measResultUTRA_FDD_r16__Format : measResultUTRA_FDD_r16__Type t_Format

type measResultListUTRA_FDD_r16__Type = measResultUTRA_FDD_r16__Type list

val measResultListUTRA_FDD_r16__Format :
  measResultListUTRA_FDD_r16__Type t_Format

type aRFCN_ValueEUTRA__Type = int

val aRFCN_ValueEUTRA__Format : int t_Format

type measResult2EUTRA__Type = { measResult2EUTRA__carrierFreq : aRFCN_ValueEUTRA__Type;
                                measResult2EUTRA__measResultServingCell : 
                                measResultEUTRA__Type option;
                                measResult2EUTRA__measResultBestNeighCell : 
                                measResultEUTRA__Type option }

val measResult2EUTRA__root_list : seq_elem list

val measResult2EUTRA__ext_list : typ list

type measResult2EUTRA__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val measResult2EUTRA__root_Format_list : measResult2EUTRA__root_Format_Type

type measResult2EUTRA__ext_Format_Type = unit t_Format

val measResult2EUTRA__ext_Format_list : measResult2EUTRA__ext_Format_Type

type measResult2EUTRA__list_type = seq_type * seq_ext_type

val measResult2EUTRA__list_format : measResult2EUTRA__list_type t_Format

val measResult2EUTRA__F1 :
  measResult2EUTRA__Type -> measResult2EUTRA__list_type

val measResult2EUTRA__F2 :
  measResult2EUTRA__list_type -> measResult2EUTRA__Type

val measResult2EUTRA__Format : measResult2EUTRA__Type t_Format

type measResultServFreqListEUTRA_SCG__Type = measResult2EUTRA__Type list

val measResultServFreqListEUTRA_SCG__Format :
  measResultServFreqListEUTRA_SCG__Type t_Format

type aRFCN_ValueNR__Type = int

val aRFCN_ValueNR__Format : int t_Format

type measResult2NR__Type = { measResult2NR__ssbFrequency : aRFCN_ValueNR__Type
                                                           option;
                             measResult2NR__refFreqCSI_RS : aRFCN_ValueNR__Type
                                                            option;
                             measResult2NR__measResultServingCell : measResultNR__Type
                                                                    option;
                             measResult2NR__measResultNeighCellListNR : 
                             measResultListNR__Type option }

val measResult2NR__root_list : seq_elem list

val measResult2NR__ext_list : typ list

type measResult2NR__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

val measResult2NR__root_Format_list : measResult2NR__root_Format_Type

type measResult2NR__ext_Format_Type = unit t_Format

val measResult2NR__ext_Format_list : measResult2NR__ext_Format_Type

type measResult2NR__list_type = seq_type * seq_ext_type

val measResult2NR__list_format : measResult2NR__list_type t_Format

val measResult2NR__F1 : measResult2NR__Type -> measResult2NR__list_type

val measResult2NR__F2 : measResult2NR__list_type -> measResult2NR__Type

val measResult2NR__Format : measResult2NR__Type t_Format

type measResultServFreqListNR_SCG__Type = measResult2NR__Type list

val measResultServFreqListNR_SCG__Format :
  measResultServFreqListNR_SCG__Type t_Format

type eUTRA_PhysCellId__Type = int

val eUTRA_PhysCellId__Format : int t_Format

type measResultSFTD_EUTRA__Type = { measResultSFTD_EUTRA__eutra_PhysCellId : 
                                    eUTRA_PhysCellId__Type;
                                    measResultSFTD_EUTRA__sfn_OffsetResult : 
                                    int;
                                    measResultSFTD_EUTRA__frameBoundaryOffsetResult : 
                                    int;
                                    measResultSFTD_EUTRA__rsrp_Result : 
                                    rSRP_Range__Type option }

val measResultSFTD_EUTRA__list : seq_elem list

val measResultSFTD_EUTRA__sfn_OffsetResult__Format : int t_Format

val measResultSFTD_EUTRA__frameBoundaryOffsetResult__Format : int t_Format

type measResultSFTD_EUTRA__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

val measResultSFTD_EUTRA__Format_list : measResultSFTD_EUTRA__Format_Type

val measResultSFTD_EUTRA__list__Format : seq_type t_Format

val measResultSFTD_EUTRA__F1 :
  measResultSFTD_EUTRA__Type ->
  eUTRA_PhysCellId__Type * (int * (int * (rSRP_Range__Type option * unit)))

val measResultSFTD_EUTRA__F2 : seq_type -> measResultSFTD_EUTRA__Type

val measResultSFTD_EUTRA__Format : measResultSFTD_EUTRA__Type t_Format

type measResultCellSFTD_NR__Type = { measResultCellSFTD_NR__physCellId : 
                                     physCellId__Type;
                                     measResultCellSFTD_NR__sfn_OffsetResult : 
                                     int;
                                     measResultCellSFTD_NR__frameBoundaryOffsetResult : 
                                     int;
                                     measResultCellSFTD_NR__rsrp_Result : 
                                     rSRP_Range__Type option }

val measResultCellSFTD_NR__list : seq_elem list

val measResultCellSFTD_NR__sfn_OffsetResult__Format : int t_Format

val measResultCellSFTD_NR__frameBoundaryOffsetResult__Format : int t_Format

type measResultCellSFTD_NR__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

val measResultCellSFTD_NR__Format_list : measResultCellSFTD_NR__Format_Type

val measResultCellSFTD_NR__list__Format : seq_type t_Format

val measResultCellSFTD_NR__F1 :
  measResultCellSFTD_NR__Type ->
  physCellId__Type * (int * (int * (rSRP_Range__Type option * unit)))

val measResultCellSFTD_NR__F2 : seq_type -> measResultCellSFTD_NR__Type

val measResultCellSFTD_NR__Format : measResultCellSFTD_NR__Type t_Format

type measResultCellListSFTD_NR__Type = measResultCellSFTD_NR__Type list

val measResultCellListSFTD_NR__Format :
  measResultCellListSFTD_NR__Type t_Format

type rSSI_Range_r16__Type = int

val rSSI_Range_r16__Format : int t_Format

type measResultForRSSI_r16__Type = { measResultForRSSI_r16__rssi_Result_r16 : 
                                     rSSI_Range_r16__Type;
                                     measResultForRSSI_r16__channelOccupancy_r16 : 
                                     int }

val measResultForRSSI_r16__list : seq_elem list

val measResultForRSSI_r16__channelOccupancy_r16__Format : int t_Format

type measResultForRSSI_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val measResultForRSSI_r16__Format_list : measResultForRSSI_r16__Format_Type

val measResultForRSSI_r16__list__Format : seq_type t_Format

val measResultForRSSI_r16__F1 :
  measResultForRSSI_r16__Type -> rSSI_Range_r16__Type * (int * unit)

val measResultForRSSI_r16__F2 : seq_type -> measResultForRSSI_r16__Type

val measResultForRSSI_r16__Format : measResultForRSSI_r16__Type t_Format

type commonLocationInfo_r16__Type = { commonLocationInfo_r16__gnss_TOD_msec_r16 : 
                                      octet_string option;
                                      commonLocationInfo_r16__locationTimestamp_r16 : 
                                      octet_string option;
                                      commonLocationInfo_r16__locationCoordinate_r16 : 
                                      octet_string option;
                                      commonLocationInfo_r16__locationError_r16 : 
                                      octet_string option;
                                      commonLocationInfo_r16__locationSource_r16 : 
                                      octet_string option;
                                      commonLocationInfo_r16__velocityEstimate_r16 : 
                                      octet_string option }

val commonLocationInfo_r16__list : seq_elem list

type commonLocationInfo_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))))

val commonLocationInfo_r16__Format_list : commonLocationInfo_r16__Format_Type

val commonLocationInfo_r16__list__Format : seq_type t_Format

val commonLocationInfo_r16__F1 :
  commonLocationInfo_r16__Type -> octet_string option * (octet_string
  option * (octet_string option * (octet_string option * (octet_string
  option * (octet_string option * unit)))))

val commonLocationInfo_r16__F2 : seq_type -> commonLocationInfo_r16__Type

val commonLocationInfo_r16__Format : commonLocationInfo_r16__Type t_Format

type logMeasResultBT_r16__bt_Addr_r16__Type = bit_string_fixed

type logMeasResultBT_r16__Type = { logMeasResultBT_r16__bt_Addr_r16 : 
                                   logMeasResultBT_r16__bt_Addr_r16__Type;
                                   logMeasResultBT_r16__rssi_BT_r16 : 
                                   int option }

val logMeasResultBT_r16__root_list : seq_elem list

val logMeasResultBT_r16__ext_list : typ list

val logMeasResultBT_r16__bt_Addr_r16__Format :
  logMeasResultBT_r16__bt_Addr_r16__Type t_Format

val logMeasResultBT_r16__rssi_BT_r16__Format : int t_Format

type logMeasResultBT_r16__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val logMeasResultBT_r16__root_Format_list :
  logMeasResultBT_r16__root_Format_Type

type logMeasResultBT_r16__ext_Format_Type = unit t_Format

val logMeasResultBT_r16__ext_Format_list : logMeasResultBT_r16__ext_Format_Type

type logMeasResultBT_r16__list_type = seq_type * seq_ext_type

val logMeasResultBT_r16__list_format : logMeasResultBT_r16__list_type t_Format

val logMeasResultBT_r16__F1 :
  logMeasResultBT_r16__Type -> logMeasResultBT_r16__list_type

val logMeasResultBT_r16__F2 :
  logMeasResultBT_r16__list_type -> logMeasResultBT_r16__Type

val logMeasResultBT_r16__Format : logMeasResultBT_r16__Type t_Format

type logMeasResultListBT_r16__Type = logMeasResultBT_r16__Type list

val logMeasResultListBT_r16__Format : logMeasResultListBT_r16__Type t_Format

type wLAN_Identifiers_r16__ssid_r16__Type = octet_string

type wLAN_Identifiers_r16__bssid_r16__Type = octet_string

type wLAN_Identifiers_r16__hessid_r16__Type = octet_string

type wLAN_Identifiers_r16__Type = { wLAN_Identifiers_r16__ssid_r16 : wLAN_Identifiers_r16__ssid_r16__Type
                                                                     option;
                                    wLAN_Identifiers_r16__bssid_r16 : 
                                    wLAN_Identifiers_r16__bssid_r16__Type
                                    option;
                                    wLAN_Identifiers_r16__hessid_r16 : 
                                    wLAN_Identifiers_r16__hessid_r16__Type
                                    option }

val wLAN_Identifiers_r16__root_list : seq_elem list

val wLAN_Identifiers_r16__ext_list : typ list

val wLAN_Identifiers_r16__ssid_r16__Format :
  wLAN_Identifiers_r16__ssid_r16__Type t_Format

val wLAN_Identifiers_r16__bssid_r16__Format :
  wLAN_Identifiers_r16__bssid_r16__Type t_Format

val wLAN_Identifiers_r16__hessid_r16__Format :
  wLAN_Identifiers_r16__hessid_r16__Type t_Format

type wLAN_Identifiers_r16__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val wLAN_Identifiers_r16__root_Format_list :
  wLAN_Identifiers_r16__root_Format_Type

type wLAN_Identifiers_r16__ext_Format_Type = unit t_Format

val wLAN_Identifiers_r16__ext_Format_list :
  wLAN_Identifiers_r16__ext_Format_Type

type wLAN_Identifiers_r16__list_type = seq_type * seq_ext_type

val wLAN_Identifiers_r16__list_format :
  wLAN_Identifiers_r16__list_type t_Format

val wLAN_Identifiers_r16__F1 :
  wLAN_Identifiers_r16__Type -> wLAN_Identifiers_r16__list_type

val wLAN_Identifiers_r16__F2 :
  wLAN_Identifiers_r16__list_type -> wLAN_Identifiers_r16__Type

val wLAN_Identifiers_r16__Format : wLAN_Identifiers_r16__Type t_Format

type wLAN_RSSI_Range_r16__Type = int

val wLAN_RSSI_Range_r16__Format : int t_Format

type wLAN_RTT_r16__rttUnits_r16__root__Type =
| WLAN_RTT_r16__rttUnits_r16__root__microseconds
| WLAN_RTT_r16__rttUnits_r16__root__hundredsofnanoseconds
| WLAN_RTT_r16__rttUnits_r16__root__tensofnanoseconds
| WLAN_RTT_r16__rttUnits_r16__root__nanoseconds
| WLAN_RTT_r16__rttUnits_r16__root__tenthsofnanoseconds

val wLAN_RTT_r16__rttUnits_r16__root__nat__Format : int t_Format

val wLAN_RTT_r16__rttUnits_r16__root__F1 :
  wLAN_RTT_r16__rttUnits_r16__root__Type -> int

val wLAN_RTT_r16__rttUnits_r16__root__F2 :
  int -> wLAN_RTT_r16__rttUnits_r16__root__Type

type wLAN_RTT_r16__rttUnits_r16__ext__Type = empty_set

type wLAN_RTT_r16__rttUnits_r16__Type =
  (wLAN_RTT_r16__rttUnits_r16__root__Type,
  wLAN_RTT_r16__rttUnits_r16__ext__Type) sum

type wLAN_RTT_r16__Type = { wLAN_RTT_r16__rttValue_r16 : int;
                            wLAN_RTT_r16__rttUnits_r16 : wLAN_RTT_r16__rttUnits_r16__Type;
                            wLAN_RTT_r16__rttAccuracy_r16 : int option }

val wLAN_RTT_r16__root_list : seq_elem list

val wLAN_RTT_r16__ext_list : typ list

val wLAN_RTT_r16__rttValue_r16__Format : int t_Format

val wLAN_RTT_r16__rttUnits_r16__root__Format :
  wLAN_RTT_r16__rttUnits_r16__root__Type t_Format

val wLAN_RTT_r16__rttUnits_r16__ext__Format :
  wLAN_RTT_r16__rttUnits_r16__ext__Type t_Format

val wLAN_RTT_r16__rttUnits_r16__Format :
  wLAN_RTT_r16__rttUnits_r16__Type t_Format

val wLAN_RTT_r16__rttAccuracy_r16__Format : int t_Format

type wLAN_RTT_r16__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val wLAN_RTT_r16__root_Format_list : wLAN_RTT_r16__root_Format_Type

type wLAN_RTT_r16__ext_Format_Type = unit t_Format

val wLAN_RTT_r16__ext_Format_list : wLAN_RTT_r16__ext_Format_Type

type wLAN_RTT_r16__list_type = seq_type * seq_ext_type

val wLAN_RTT_r16__list_format : wLAN_RTT_r16__list_type t_Format

val wLAN_RTT_r16__F1 : wLAN_RTT_r16__Type -> wLAN_RTT_r16__list_type

val wLAN_RTT_r16__F2 : wLAN_RTT_r16__list_type -> wLAN_RTT_r16__Type

val wLAN_RTT_r16__Format : wLAN_RTT_r16__Type t_Format

type logMeasResultWLAN_r16__Type = { logMeasResultWLAN_r16__wlan_Identifiers_r16 : 
                                     wLAN_Identifiers_r16__Type;
                                     logMeasResultWLAN_r16__rssiWLAN_r16 : 
                                     wLAN_RSSI_Range_r16__Type option;
                                     logMeasResultWLAN_r16__rtt_WLAN_r16 : 
                                     wLAN_RTT_r16__Type option }

val logMeasResultWLAN_r16__root_list : seq_elem list

val logMeasResultWLAN_r16__ext_list : typ list

type logMeasResultWLAN_r16__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val logMeasResultWLAN_r16__root_Format_list :
  logMeasResultWLAN_r16__root_Format_Type

type logMeasResultWLAN_r16__ext_Format_Type = unit t_Format

val logMeasResultWLAN_r16__ext_Format_list :
  logMeasResultWLAN_r16__ext_Format_Type

type logMeasResultWLAN_r16__list_type = seq_type * seq_ext_type

val logMeasResultWLAN_r16__list_format :
  logMeasResultWLAN_r16__list_type t_Format

val logMeasResultWLAN_r16__F1 :
  logMeasResultWLAN_r16__Type -> logMeasResultWLAN_r16__list_type

val logMeasResultWLAN_r16__F2 :
  logMeasResultWLAN_r16__list_type -> logMeasResultWLAN_r16__Type

val logMeasResultWLAN_r16__Format : logMeasResultWLAN_r16__Type t_Format

type logMeasResultListWLAN_r16__Type = logMeasResultWLAN_r16__Type list

val logMeasResultListWLAN_r16__Format :
  logMeasResultListWLAN_r16__Type t_Format

type sensor_LocationInfo_r16__Type = { sensor_LocationInfo_r16__sensor_MeasurementInformation_r16 : 
                                       octet_string option;
                                       sensor_LocationInfo_r16__sensor_MotionInformation_r16 : 
                                       octet_string option }

val sensor_LocationInfo_r16__root_list : seq_elem list

val sensor_LocationInfo_r16__ext_list : typ list

type sensor_LocationInfo_r16__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val sensor_LocationInfo_r16__root_Format_list :
  sensor_LocationInfo_r16__root_Format_Type

type sensor_LocationInfo_r16__ext_Format_Type = unit t_Format

val sensor_LocationInfo_r16__ext_Format_list :
  sensor_LocationInfo_r16__ext_Format_Type

type sensor_LocationInfo_r16__list_type = seq_type * seq_ext_type

val sensor_LocationInfo_r16__list_format :
  sensor_LocationInfo_r16__list_type t_Format

val sensor_LocationInfo_r16__F1 :
  sensor_LocationInfo_r16__Type -> sensor_LocationInfo_r16__list_type

val sensor_LocationInfo_r16__F2 :
  sensor_LocationInfo_r16__list_type -> sensor_LocationInfo_r16__Type

val sensor_LocationInfo_r16__Format : sensor_LocationInfo_r16__Type t_Format

type locationInfo_r16__Type = { locationInfo_r16__commonLocationInfo_r16 : 
                                commonLocationInfo_r16__Type option;
                                locationInfo_r16__bt_LocationInfo_r16 : 
                                logMeasResultListBT_r16__Type option;
                                locationInfo_r16__wlan_LocationInfo_r16 : 
                                logMeasResultListWLAN_r16__Type option;
                                locationInfo_r16__sensor_LocationInfo_r16 : 
                                sensor_LocationInfo_r16__Type option }

val locationInfo_r16__root_list : seq_elem list

val locationInfo_r16__ext_list : typ list

type locationInfo_r16__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

val locationInfo_r16__root_Format_list : locationInfo_r16__root_Format_Type

type locationInfo_r16__ext_Format_Type = unit t_Format

val locationInfo_r16__ext_Format_list : locationInfo_r16__ext_Format_Type

type locationInfo_r16__list_type = seq_type * seq_ext_type

val locationInfo_r16__list_format : locationInfo_r16__list_type t_Format

val locationInfo_r16__F1 :
  locationInfo_r16__Type -> locationInfo_r16__list_type

val locationInfo_r16__F2 :
  locationInfo_r16__list_type -> locationInfo_r16__Type

val locationInfo_r16__Format : locationInfo_r16__Type t_Format

type dRB_Identity__Type = int

val dRB_Identity__Format : int t_Format

type uL_PDCP_DelayValueResult_r16__Type = { uL_PDCP_DelayValueResult_r16__drb_Id_r16 : 
                                            dRB_Identity__Type;
                                            uL_PDCP_DelayValueResult_r16__averageDelay_r16 : 
                                            int }

val uL_PDCP_DelayValueResult_r16__root_list : seq_elem list

val uL_PDCP_DelayValueResult_r16__ext_list : typ list

val uL_PDCP_DelayValueResult_r16__averageDelay_r16__Format : int t_Format

type uL_PDCP_DelayValueResult_r16__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val uL_PDCP_DelayValueResult_r16__root_Format_list :
  uL_PDCP_DelayValueResult_r16__root_Format_Type

type uL_PDCP_DelayValueResult_r16__ext_Format_Type = unit t_Format

val uL_PDCP_DelayValueResult_r16__ext_Format_list :
  uL_PDCP_DelayValueResult_r16__ext_Format_Type

type uL_PDCP_DelayValueResult_r16__list_type = seq_type * seq_ext_type

val uL_PDCP_DelayValueResult_r16__list_format :
  uL_PDCP_DelayValueResult_r16__list_type t_Format

val uL_PDCP_DelayValueResult_r16__F1 :
  uL_PDCP_DelayValueResult_r16__Type -> uL_PDCP_DelayValueResult_r16__list_type

val uL_PDCP_DelayValueResult_r16__F2 :
  uL_PDCP_DelayValueResult_r16__list_type -> uL_PDCP_DelayValueResult_r16__Type

val uL_PDCP_DelayValueResult_r16__Format :
  uL_PDCP_DelayValueResult_r16__Type t_Format

type uL_PDCP_DelayValueResultList_r16__Type =
  uL_PDCP_DelayValueResult_r16__Type list

val uL_PDCP_DelayValueResultList_r16__Format :
  uL_PDCP_DelayValueResultList_r16__Type t_Format

type sL_ResourcePoolID_r16__Type = int

val sL_ResourcePoolID_r16__Format : int t_Format

type sL_CBR_r16__Type = int

val sL_CBR_r16__Format : int t_Format

type measResultCBR_NR_r16__Type = { measResultCBR_NR_r16__sl_poolReportIdentity_r16 : 
                                    sL_ResourcePoolID_r16__Type;
                                    measResultCBR_NR_r16__sl_CBR_ResultsNR_r16 : 
                                    sL_CBR_r16__Type }

val measResultCBR_NR_r16__root_list : seq_elem list

val measResultCBR_NR_r16__ext_list : typ list

type measResultCBR_NR_r16__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val measResultCBR_NR_r16__root_Format_list :
  measResultCBR_NR_r16__root_Format_Type

type measResultCBR_NR_r16__ext_Format_Type = unit t_Format

val measResultCBR_NR_r16__ext_Format_list :
  measResultCBR_NR_r16__ext_Format_Type

type measResultCBR_NR_r16__list_type = seq_type * seq_ext_type

val measResultCBR_NR_r16__list_format :
  measResultCBR_NR_r16__list_type t_Format

val measResultCBR_NR_r16__F1 :
  measResultCBR_NR_r16__Type -> measResultCBR_NR_r16__list_type

val measResultCBR_NR_r16__F2 :
  measResultCBR_NR_r16__list_type -> measResultCBR_NR_r16__Type

val measResultCBR_NR_r16__Format : measResultCBR_NR_r16__Type t_Format

type measResultNR_SL_r16__measResultListCBR_NR_r16__Type =
  measResultCBR_NR_r16__Type list

type measResultNR_SL_r16__Type = { measResultNR_SL_r16__measResultListCBR_NR_r16 : 
                                   measResultNR_SL_r16__measResultListCBR_NR_r16__Type }

val measResultNR_SL_r16__root_list : seq_elem list

val measResultNR_SL_r16__ext_list : typ list

val measResultNR_SL_r16__measResultListCBR_NR_r16__Format :
  measResultNR_SL_r16__measResultListCBR_NR_r16__Type t_Format

type measResultNR_SL_r16__root_Format_Type =
  seq_elem_to_format * seq_elem_to_format

val measResultNR_SL_r16__root_Format_list :
  measResultNR_SL_r16__root_Format_Type

type measResultNR_SL_r16__ext_Format_Type = unit t_Format

val measResultNR_SL_r16__ext_Format_list : measResultNR_SL_r16__ext_Format_Type

type measResultNR_SL_r16__list_type = seq_type * seq_ext_type

val measResultNR_SL_r16__list_format : measResultNR_SL_r16__list_type t_Format

val measResultNR_SL_r16__F1 :
  measResultNR_SL_r16__Type -> measResultNR_SL_r16__list_type

val measResultNR_SL_r16__F2 :
  measResultNR_SL_r16__list_type -> measResultNR_SL_r16__Type

val measResultNR_SL_r16__Format : measResultNR_SL_r16__Type t_Format

type measResultsSL_r16__measResultsListSL_r16__root__Type =
| MeasResultsSL_r16__measResultsListSL_r16__root__measResultNR_SL_r16 of 
   measResultNR_SL_r16__Type

type measResultsSL_r16__measResultsListSL_r16__ext__Type = empty_set

type measResultsSL_r16__measResultsListSL_r16__Type =
  (measResultsSL_r16__measResultsListSL_r16__root__Type,
  measResultsSL_r16__measResultsListSL_r16__ext__Type) sum

type measResultsSL_r16__Type = { measResultsSL_r16__measResultsListSL_r16 : 
                                 measResultsSL_r16__measResultsListSL_r16__Type }

val measResultsSL_r16__root_list : seq_elem list

val measResultsSL_r16__ext_list : typ list

val measResultsSL_r16__measResultsListSL_r16__root__F1 :
  measResultsSL_r16__measResultsListSL_r16__root__Type ->
  measResultNR_SL_r16__Type

val measResultsSL_r16__measResultsListSL_r16__root__F2 :
  measResultNR_SL_r16__Type ->
  measResultsSL_r16__measResultsListSL_r16__root__Type

val measResultsSL_r16__measResultsListSL_r16__root__Format :
  measResultsSL_r16__measResultsListSL_r16__root__Type t_Format

val measResultsSL_r16__measResultsListSL_r16__ext__Format :
  measResultsSL_r16__measResultsListSL_r16__ext__Type t_Format

val measResultsSL_r16__measResultsListSL_r16__Format :
  measResultsSL_r16__measResultsListSL_r16__Type t_Format

type measResultsSL_r16__root_Format_Type =
  seq_elem_to_format * seq_elem_to_format

val measResultsSL_r16__root_Format_list : measResultsSL_r16__root_Format_Type

type measResultsSL_r16__ext_Format_Type = unit t_Format

val measResultsSL_r16__ext_Format_list : measResultsSL_r16__ext_Format_Type

type measResultsSL_r16__list_type = seq_type * seq_ext_type

val measResultsSL_r16__list_format : measResultsSL_r16__list_type t_Format

val measResultsSL_r16__F1 :
  measResultsSL_r16__Type -> measResultsSL_r16__list_type

val measResultsSL_r16__F2 :
  measResultsSL_r16__list_type -> measResultsSL_r16__Type

val measResultsSL_r16__Format : measResultsSL_r16__Type t_Format

type sRS_ResourceId__Type = int

val sRS_ResourceId__Format : int t_Format

type sRS_RSRP_Range_r16__Type = int

val sRS_RSRP_Range_r16__Format : int t_Format

type measResultSRS_RSRP_r16__Type = { measResultSRS_RSRP_r16__srs_ResourceId_r16 : 
                                      sRS_ResourceId__Type;
                                      measResultSRS_RSRP_r16__srs_RSRP_Result_r16 : 
                                      sRS_RSRP_Range_r16__Type }

val measResultSRS_RSRP_r16__list : seq_elem list

type measResultSRS_RSRP_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val measResultSRS_RSRP_r16__Format_list : measResultSRS_RSRP_r16__Format_Type

val measResultSRS_RSRP_r16__list__Format : seq_type t_Format

val measResultSRS_RSRP_r16__F1 :
  measResultSRS_RSRP_r16__Type ->
  sRS_ResourceId__Type * (sRS_RSRP_Range_r16__Type * unit)

val measResultSRS_RSRP_r16__F2 : seq_type -> measResultSRS_RSRP_r16__Type

val measResultSRS_RSRP_r16__Format : measResultSRS_RSRP_r16__Type t_Format

type measResultListSRS_RSRP_r16__Type = measResultSRS_RSRP_r16__Type list

val measResultListSRS_RSRP_r16__Format :
  measResultListSRS_RSRP_r16__Type t_Format

type rSSI_ResourceId_r16__Type = int

val rSSI_ResourceId_r16__Format : int t_Format

type cLI_RSSI_Range_r16__Type = int

val cLI_RSSI_Range_r16__Format : int t_Format

type measResultCLI_RSSI_r16__Type = { measResultCLI_RSSI_r16__rssi_ResourceId_r16 : 
                                      rSSI_ResourceId_r16__Type;
                                      measResultCLI_RSSI_r16__cli_RSSI_Result_r16 : 
                                      cLI_RSSI_Range_r16__Type }

val measResultCLI_RSSI_r16__list : seq_elem list

type measResultCLI_RSSI_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val measResultCLI_RSSI_r16__Format_list : measResultCLI_RSSI_r16__Format_Type

val measResultCLI_RSSI_r16__list__Format : seq_type t_Format

val measResultCLI_RSSI_r16__F1 :
  measResultCLI_RSSI_r16__Type ->
  rSSI_ResourceId_r16__Type * (cLI_RSSI_Range_r16__Type * unit)

val measResultCLI_RSSI_r16__F2 : seq_type -> measResultCLI_RSSI_r16__Type

val measResultCLI_RSSI_r16__Format : measResultCLI_RSSI_r16__Type t_Format

type measResultListCLI_RSSI_r16__Type = measResultCLI_RSSI_r16__Type list

val measResultListCLI_RSSI_r16__Format :
  measResultListCLI_RSSI_r16__Type t_Format

type measResultCLI_r16__Type = { measResultCLI_r16__measResultListSRS_RSRP_r16 : 
                                 measResultListSRS_RSRP_r16__Type option;
                                 measResultCLI_r16__measResultListCLI_RSSI_r16 : 
                                 measResultListCLI_RSSI_r16__Type option }

val measResultCLI_r16__list : seq_elem list

type measResultCLI_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val measResultCLI_r16__Format_list : measResultCLI_r16__Format_Type

val measResultCLI_r16__list__Format : seq_type t_Format

val measResultCLI_r16__F1 :
  measResultCLI_r16__Type -> measResultListSRS_RSRP_r16__Type
  option * (measResultListCLI_RSSI_r16__Type option * unit)

val measResultCLI_r16__F2 : seq_type -> measResultCLI_r16__Type

val measResultCLI_r16__Format : measResultCLI_r16__Type t_Format

type rxTxTimeDiff_r17__Type = { rxTxTimeDiff_r17__result_k5_r17 : int option }

val rxTxTimeDiff_r17__root_list : seq_elem list

val rxTxTimeDiff_r17__ext_list : typ list

val rxTxTimeDiff_r17__result_k5_r17__Format : int t_Format

type rxTxTimeDiff_r17__root_Format_Type =
  seq_elem_to_format * seq_elem_to_format

val rxTxTimeDiff_r17__root_Format_list : rxTxTimeDiff_r17__root_Format_Type

type rxTxTimeDiff_r17__ext_Format_Type = unit t_Format

val rxTxTimeDiff_r17__ext_Format_list : rxTxTimeDiff_r17__ext_Format_Type

type rxTxTimeDiff_r17__list_type = seq_type * seq_ext_type

val rxTxTimeDiff_r17__list_format : rxTxTimeDiff_r17__list_type t_Format

val rxTxTimeDiff_r17__F1 :
  rxTxTimeDiff_r17__Type -> rxTxTimeDiff_r17__list_type

val rxTxTimeDiff_r17__F2 :
  rxTxTimeDiff_r17__list_type -> rxTxTimeDiff_r17__Type

val rxTxTimeDiff_r17__Format : rxTxTimeDiff_r17__Type t_Format

type measResultRxTxTimeDiff_r17__Type = { measResultRxTxTimeDiff_r17__rxTxTimeDiff_ue_r17 : 
                                          rxTxTimeDiff_r17__Type option }

val measResultRxTxTimeDiff_r17__root_list : seq_elem list

val measResultRxTxTimeDiff_r17__ext_list : typ list

type measResultRxTxTimeDiff_r17__root_Format_Type =
  seq_elem_to_format * seq_elem_to_format

val measResultRxTxTimeDiff_r17__root_Format_list :
  measResultRxTxTimeDiff_r17__root_Format_Type

type measResultRxTxTimeDiff_r17__ext_Format_Type = unit t_Format

val measResultRxTxTimeDiff_r17__ext_Format_list :
  measResultRxTxTimeDiff_r17__ext_Format_Type

type measResultRxTxTimeDiff_r17__list_type = seq_type * seq_ext_type

val measResultRxTxTimeDiff_r17__list_format :
  measResultRxTxTimeDiff_r17__list_type t_Format

val measResultRxTxTimeDiff_r17__F1 :
  measResultRxTxTimeDiff_r17__Type -> measResultRxTxTimeDiff_r17__list_type

val measResultRxTxTimeDiff_r17__F2 :
  measResultRxTxTimeDiff_r17__list_type -> measResultRxTxTimeDiff_r17__Type

val measResultRxTxTimeDiff_r17__Format :
  measResultRxTxTimeDiff_r17__Type t_Format

type uL_PDCP_ExcessDelayResult_r17__Type = { uL_PDCP_ExcessDelayResult_r17__drb_Id_r17 : 
                                             dRB_Identity__Type;
                                             uL_PDCP_ExcessDelayResult_r17__excessDelay_r17 : 
                                             int }

val uL_PDCP_ExcessDelayResult_r17__root_list : seq_elem list

val uL_PDCP_ExcessDelayResult_r17__ext_list : typ list

val uL_PDCP_ExcessDelayResult_r17__excessDelay_r17__Format : int t_Format

type uL_PDCP_ExcessDelayResult_r17__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val uL_PDCP_ExcessDelayResult_r17__root_Format_list :
  uL_PDCP_ExcessDelayResult_r17__root_Format_Type

type uL_PDCP_ExcessDelayResult_r17__ext_Format_Type = unit t_Format

val uL_PDCP_ExcessDelayResult_r17__ext_Format_list :
  uL_PDCP_ExcessDelayResult_r17__ext_Format_Type

type uL_PDCP_ExcessDelayResult_r17__list_type = seq_type * seq_ext_type

val uL_PDCP_ExcessDelayResult_r17__list_format :
  uL_PDCP_ExcessDelayResult_r17__list_type t_Format

val uL_PDCP_ExcessDelayResult_r17__F1 :
  uL_PDCP_ExcessDelayResult_r17__Type ->
  uL_PDCP_ExcessDelayResult_r17__list_type

val uL_PDCP_ExcessDelayResult_r17__F2 :
  uL_PDCP_ExcessDelayResult_r17__list_type ->
  uL_PDCP_ExcessDelayResult_r17__Type

val uL_PDCP_ExcessDelayResult_r17__Format :
  uL_PDCP_ExcessDelayResult_r17__Type t_Format

type uL_PDCP_ExcessDelayResultList_r17__Type =
  uL_PDCP_ExcessDelayResult_r17__Type list

val uL_PDCP_ExcessDelayResultList_r17__Format :
  uL_PDCP_ExcessDelayResultList_r17__Type t_Format

type measResults__measResultNeighCells__root__Type =
| MeasResults__measResultNeighCells__root__measResultListNR of measResultListNR__Type

type measResults__measResultNeighCells__ext__Type =
| MeasResults__measResultNeighCells__ext__measResultListEUTRA of measResultListEUTRA__Type
| MeasResults__measResultNeighCells__ext__measResultListUTRA_FDD_r16 of 
   measResultListUTRA_FDD_r16__Type
| MeasResults__measResultNeighCells__ext__sl_MeasResultsCandRelay_r17 of 
   octet_string

type measResults__measResultNeighCells__Type =
  (measResults__measResultNeighCells__root__Type,
  measResults__measResultNeighCells__ext__Type) sum

type measResults__ext0O__Type = { measResults__ext0O__measResultServFreqListEUTRA_SCG : 
                                  measResultServFreqListEUTRA_SCG__Type option;
                                  measResults__ext0O__measResultServFreqListNR_SCG : 
                                  measResultServFreqListNR_SCG__Type option;
                                  measResults__ext0O__measResultSFTD_EUTRA : 
                                  measResultSFTD_EUTRA__Type option;
                                  measResults__ext0O__measResultSFTD_NR : 
                                  measResultCellSFTD_NR__Type option }

val measResults__ext0O__list : seq_elem list

type measResults__ext0__Type = measResults__ext0O__Type

type measResults__ext1O__Type = { measResults__ext1O__measResultCellListSFTD_NR : 
                                  measResultCellListSFTD_NR__Type option }

val measResults__ext1O__list : seq_elem list

type measResults__ext1__Type = measResults__ext1O__Type

type measResults__ext2O__Type = { measResults__ext2O__measResultForRSSI_r16 : 
                                  measResultForRSSI_r16__Type option;
                                  measResults__ext2O__locationInfo_r16 : 
                                  locationInfo_r16__Type option;
                                  measResults__ext2O__ul_PDCP_DelayValueResultList_r16 : 
                                  uL_PDCP_DelayValueResultList_r16__Type option;
                                  measResults__ext2O__measResultsSL_r16 : 
                                  measResultsSL_r16__Type option;
                                  measResults__ext2O__measResultCLI_r16 : 
                                  measResultCLI_r16__Type option }

val measResults__ext2O__list : seq_elem list

type measResults__ext2__Type = measResults__ext2O__Type

type measResults__ext3O__Type = { measResults__ext3O__measResultRxTxTimeDiff_r17 : 
                                  measResultRxTxTimeDiff_r17__Type option;
                                  measResults__ext3O__sl_MeasResultServingRelay_r17 : 
                                  octet_string option;
                                  measResults__ext3O__ul_PDCP_ExcessDelayResultList_r17 : 
                                  uL_PDCP_ExcessDelayResultList_r17__Type
                                  option;
                                  measResults__ext3O__coarseLocationInfo_r17 : 
                                  octet_string option }

val measResults__ext3O__list : seq_elem list

type measResults__ext3__Type = measResults__ext3O__Type

type measResults__Type = { measResults__measId : measId__Type;
                           measResults__measResultServingMOList : measResultServMOList__Type;
                           measResults__measResultNeighCells : measResults__measResultNeighCells__Type
                                                               option;
                           measResults__ext0 : measResults__ext0__Type option;
                           measResults__ext1 : measResults__ext1__Type option;
                           measResults__ext2 : measResults__ext2__Type option;
                           measResults__ext3 : measResults__ext3__Type option }

val measResults__root_list : seq_elem list

val measResults__ext_list : typ list

val measResults__measResultNeighCells__root__F1 :
  measResults__measResultNeighCells__root__Type -> measResultListNR__Type

val measResults__measResultNeighCells__root__F2 :
  measResultListNR__Type -> measResults__measResultNeighCells__root__Type

val measResults__measResultNeighCells__root__Format :
  measResults__measResultNeighCells__root__Type t_Format

val measResults__measResultNeighCells__ext__list__Format :
  (int, __) sigT t_Format

val measResults__measResultNeighCells__ext__F1 :
  measResults__measResultNeighCells__ext__Type -> choice

val measResults__measResultNeighCells__ext__F2 :
  choice -> measResults__measResultNeighCells__ext__Type

val measResults__measResultNeighCells__ext__Format :
  measResults__measResultNeighCells__ext__Type t_Format

val measResults__measResultNeighCells__Format :
  measResults__measResultNeighCells__Type t_Format

type measResults__ext0O__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

val measResults__ext0O__Format_list : measResults__ext0O__Format_Type

val measResults__ext0O__list__Format : seq_type t_Format

val measResults__ext0O__F1 :
  measResults__ext0O__Type -> measResultServFreqListEUTRA_SCG__Type
  option * (measResultServFreqListNR_SCG__Type
  option * (measResultSFTD_EUTRA__Type option * (measResultCellSFTD_NR__Type
  option * unit)))

val measResults__ext0O__F2 : seq_type -> measResults__ext0O__Type

val measResults__ext0O__Format : measResults__ext0O__Type t_Format

val measResults__ext0__check_all_none : measResults__ext0O__Type -> bool

val measResults__ext0__Format : measResults__ext0__Type t_Format

type measResults__ext1O__Format_Type = seq_elem_to_format * seq_elem_to_format

val measResults__ext1O__Format_list : measResults__ext1O__Format_Type

val measResults__ext1O__list__Format : seq_type t_Format

val measResults__ext1O__F1 :
  measResults__ext1O__Type -> measResultCellListSFTD_NR__Type option * unit

val measResults__ext1O__F2 : seq_type -> measResults__ext1O__Type

val measResults__ext1O__Format : measResults__ext1O__Type t_Format

val measResults__ext1__check_all_none : measResults__ext1O__Type -> bool

val measResults__ext1__Format : measResults__ext1__Type t_Format

type measResults__ext2O__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))))

val measResults__ext2O__Format_list : measResults__ext2O__Format_Type

val measResults__ext2O__list__Format : seq_type t_Format

val measResults__ext2O__F1 :
  measResults__ext2O__Type -> measResultForRSSI_r16__Type
  option * (locationInfo_r16__Type
  option * (uL_PDCP_DelayValueResultList_r16__Type
  option * (measResultsSL_r16__Type option * (measResultCLI_r16__Type
  option * unit))))

val measResults__ext2O__F2 : seq_type -> measResults__ext2O__Type

val measResults__ext2O__Format : measResults__ext2O__Type t_Format

val measResults__ext2__check_all_none : measResults__ext2O__Type -> bool

val measResults__ext2__Format : measResults__ext2__Type t_Format

type measResults__ext3O__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

val measResults__ext3O__Format_list : measResults__ext3O__Format_Type

val measResults__ext3O__list__Format : seq_type t_Format

val measResults__ext3O__F1 :
  measResults__ext3O__Type -> measResultRxTxTimeDiff_r17__Type
  option * (octet_string option * (uL_PDCP_ExcessDelayResultList_r17__Type
  option * (octet_string option * unit)))

val measResults__ext3O__F2 : seq_type -> measResults__ext3O__Type

val measResults__ext3O__Format : measResults__ext3O__Type t_Format

val measResults__ext3__check_all_none : measResults__ext3O__Type -> bool

val measResults__ext3__Format : measResults__ext3__Type t_Format

type measResults__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val measResults__root_Format_list : measResults__root_Format_Type

type measResults__ext_Format_Type =
  measResults__ext0__Type t_Format * (measResults__ext1__Type
  t_Format * (measResults__ext2__Type t_Format * (measResults__ext3__Type
  t_Format * unit t_Format)))

val measResults__ext_Format_list : measResults__ext_Format_Type

type measResults__list_type = seq_type * seq_ext_type

val measResults__list_format : measResults__list_type t_Format

val measResults__F1 : measResults__Type -> measResults__list_type

val measResults__F2 : measResults__list_type -> measResults__Type

val measResults__Format : measResults__Type t_Format

type measurementReport_IEs__nonCriticalExtension__Type =
| Make__MeasurementReport_IEs__nonCriticalExtension__Type

type measurementReport_IEs__Type = { measurementReport_IEs__measResults : 
                                     measResults__Type;
                                     measurementReport_IEs__lateNonCriticalExtension : 
                                     octet_string option;
                                     measurementReport_IEs__nonCriticalExtension : 
                                     measurementReport_IEs__nonCriticalExtension__Type
                                     option }

val measurementReport_IEs__list : seq_elem list

val measurementReport_IEs__nonCriticalExtension__Format :
  measurementReport_IEs__nonCriticalExtension__Type t_Format

type measurementReport_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val measurementReport_IEs__Format_list : measurementReport_IEs__Format_Type

val measurementReport_IEs__list__Format : seq_type t_Format

val measurementReport_IEs__F1 :
  measurementReport_IEs__Type -> measResults__Type * (octet_string
  option * (measurementReport_IEs__nonCriticalExtension__Type option * unit))

val measurementReport_IEs__F2 : seq_type -> measurementReport_IEs__Type

val measurementReport_IEs__Format : measurementReport_IEs__Type t_Format

type measurementReport__criticalExtensions__criticalExtensionsFuture__Type =
| Make__MeasurementReport__criticalExtensions__criticalExtensionsFuture__Type

type measurementReport__criticalExtensions__Type =
| MeasurementReport__criticalExtensions__measurementReport of measurementReport_IEs__Type
| MeasurementReport__criticalExtensions__criticalExtensionsFuture of measurementReport__criticalExtensions__criticalExtensionsFuture__Type

type measurementReport__Type = { measurementReport__criticalExtensions : 
                                 measurementReport__criticalExtensions__Type }

val measurementReport__list : seq_elem list

val measurementReport__criticalExtensions__criticalExtensionsFuture__Format :
  measurementReport__criticalExtensions__criticalExtensionsFuture__Type
  t_Format

val measurementReport__criticalExtensions__list__Format :
  (int, __) sigT t_Format

val measurementReport__criticalExtensions__F1 :
  measurementReport__criticalExtensions__Type -> choice

val measurementReport__criticalExtensions__F2 :
  choice -> measurementReport__criticalExtensions__Type

val measurementReport__criticalExtensions__Format :
  measurementReport__criticalExtensions__Type t_Format

type measurementReport__Format_Type = seq_elem_to_format * seq_elem_to_format

val measurementReport__Format_list : measurementReport__Format_Type

val measurementReport__list__Format : seq_type t_Format

val measurementReport__F1 :
  measurementReport__Type -> measurementReport__criticalExtensions__Type * unit

val measurementReport__F2 : seq_type -> measurementReport__Type

val measurementReport__Format : measurementReport__Type t_Format

type rRC_TransactionIdentifier__Type = int

val rRC_TransactionIdentifier__Format : int t_Format

type bWP_Id__Type = int

val bWP_Id__Format : int t_Format

type uplinkTxDirectCurrentBWP__Type = { uplinkTxDirectCurrentBWP__bwp_Id : 
                                        bWP_Id__Type;
                                        uplinkTxDirectCurrentBWP__shift7dot5kHz : 
                                        bool;
                                        uplinkTxDirectCurrentBWP__txDirectCurrentLocation : 
                                        int }

val uplinkTxDirectCurrentBWP__list : seq_elem list

val uplinkTxDirectCurrentBWP__txDirectCurrentLocation__Format : int t_Format

type uplinkTxDirectCurrentBWP__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val uplinkTxDirectCurrentBWP__Format_list :
  uplinkTxDirectCurrentBWP__Format_Type

val uplinkTxDirectCurrentBWP__list__Format : seq_type t_Format

val uplinkTxDirectCurrentBWP__F1 :
  uplinkTxDirectCurrentBWP__Type -> bWP_Id__Type * (bool * (int * unit))

val uplinkTxDirectCurrentBWP__F2 : seq_type -> uplinkTxDirectCurrentBWP__Type

val uplinkTxDirectCurrentBWP__Format : uplinkTxDirectCurrentBWP__Type t_Format

type uplinkTxDirectCurrentCell__uplinkDirectCurrentBWP__Type =
  uplinkTxDirectCurrentBWP__Type list

type uplinkTxDirectCurrentCell__ext0O__uplinkDirectCurrentBWP_SUL__Type =
  uplinkTxDirectCurrentBWP__Type list

type uplinkTxDirectCurrentCell__ext0O__Type = { uplinkTxDirectCurrentCell__ext0O__uplinkDirectCurrentBWP_SUL : 
                                                uplinkTxDirectCurrentCell__ext0O__uplinkDirectCurrentBWP_SUL__Type
                                                option }

val uplinkTxDirectCurrentCell__ext0O__list : seq_elem list

type uplinkTxDirectCurrentCell__ext0__Type =
  uplinkTxDirectCurrentCell__ext0O__Type

type uplinkTxDirectCurrentCell__Type = { uplinkTxDirectCurrentCell__servCellIndex : 
                                         servCellIndex__Type;
                                         uplinkTxDirectCurrentCell__uplinkDirectCurrentBWP : 
                                         uplinkTxDirectCurrentCell__uplinkDirectCurrentBWP__Type;
                                         uplinkTxDirectCurrentCell__ext0 : 
                                         uplinkTxDirectCurrentCell__ext0__Type
                                         option }

val uplinkTxDirectCurrentCell__root_list : seq_elem list

val uplinkTxDirectCurrentCell__ext_list : typ list

val uplinkTxDirectCurrentCell__uplinkDirectCurrentBWP__Format :
  uplinkTxDirectCurrentCell__uplinkDirectCurrentBWP__Type t_Format

val uplinkTxDirectCurrentCell__ext0O__uplinkDirectCurrentBWP_SUL__Format :
  uplinkTxDirectCurrentCell__ext0O__uplinkDirectCurrentBWP_SUL__Type t_Format

type uplinkTxDirectCurrentCell__ext0O__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val uplinkTxDirectCurrentCell__ext0O__Format_list :
  uplinkTxDirectCurrentCell__ext0O__Format_Type

val uplinkTxDirectCurrentCell__ext0O__list__Format : seq_type t_Format

val uplinkTxDirectCurrentCell__ext0O__F1 :
  uplinkTxDirectCurrentCell__ext0O__Type ->
  uplinkTxDirectCurrentCell__ext0O__uplinkDirectCurrentBWP_SUL__Type
  option * unit

val uplinkTxDirectCurrentCell__ext0O__F2 :
  seq_type -> uplinkTxDirectCurrentCell__ext0O__Type

val uplinkTxDirectCurrentCell__ext0O__Format :
  uplinkTxDirectCurrentCell__ext0O__Type t_Format

val uplinkTxDirectCurrentCell__ext0__check_all_none :
  uplinkTxDirectCurrentCell__ext0O__Type -> bool

val uplinkTxDirectCurrentCell__ext0__Format :
  uplinkTxDirectCurrentCell__ext0__Type t_Format

type uplinkTxDirectCurrentCell__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val uplinkTxDirectCurrentCell__root_Format_list :
  uplinkTxDirectCurrentCell__root_Format_Type

type uplinkTxDirectCurrentCell__ext_Format_Type =
  uplinkTxDirectCurrentCell__ext0__Type t_Format * unit t_Format

val uplinkTxDirectCurrentCell__ext_Format_list :
  uplinkTxDirectCurrentCell__ext_Format_Type

type uplinkTxDirectCurrentCell__list_type = seq_type * seq_ext_type

val uplinkTxDirectCurrentCell__list_format :
  uplinkTxDirectCurrentCell__list_type t_Format

val uplinkTxDirectCurrentCell__F1 :
  uplinkTxDirectCurrentCell__Type -> uplinkTxDirectCurrentCell__list_type

val uplinkTxDirectCurrentCell__F2 :
  uplinkTxDirectCurrentCell__list_type -> uplinkTxDirectCurrentCell__Type

val uplinkTxDirectCurrentCell__Format :
  uplinkTxDirectCurrentCell__Type t_Format

type uplinkTxDirectCurrentList__Type = uplinkTxDirectCurrentCell__Type list

val uplinkTxDirectCurrentList__Format :
  uplinkTxDirectCurrentList__Type t_Format

type uE_MeasurementsAvailable_r16__logMeasAvailable_r16__Type =
| UE_MeasurementsAvailable_r16__logMeasAvailable_r16__true

val uE_MeasurementsAvailable_r16__logMeasAvailable_r16__nat__Format :
  int t_Format

val uE_MeasurementsAvailable_r16__logMeasAvailable_r16__F1 :
  uE_MeasurementsAvailable_r16__logMeasAvailable_r16__Type -> int

val uE_MeasurementsAvailable_r16__logMeasAvailable_r16__F2 :
  int -> uE_MeasurementsAvailable_r16__logMeasAvailable_r16__Type

type uE_MeasurementsAvailable_r16__logMeasAvailableBT_r16__Type =
| UE_MeasurementsAvailable_r16__logMeasAvailableBT_r16__true

val uE_MeasurementsAvailable_r16__logMeasAvailableBT_r16__nat__Format :
  int t_Format

val uE_MeasurementsAvailable_r16__logMeasAvailableBT_r16__F1 :
  uE_MeasurementsAvailable_r16__logMeasAvailableBT_r16__Type -> int

val uE_MeasurementsAvailable_r16__logMeasAvailableBT_r16__F2 :
  int -> uE_MeasurementsAvailable_r16__logMeasAvailableBT_r16__Type

type uE_MeasurementsAvailable_r16__logMeasAvailableWLAN_r16__Type =
| UE_MeasurementsAvailable_r16__logMeasAvailableWLAN_r16__true

val uE_MeasurementsAvailable_r16__logMeasAvailableWLAN_r16__nat__Format :
  int t_Format

val uE_MeasurementsAvailable_r16__logMeasAvailableWLAN_r16__F1 :
  uE_MeasurementsAvailable_r16__logMeasAvailableWLAN_r16__Type -> int

val uE_MeasurementsAvailable_r16__logMeasAvailableWLAN_r16__F2 :
  int -> uE_MeasurementsAvailable_r16__logMeasAvailableWLAN_r16__Type

type uE_MeasurementsAvailable_r16__connEstFailInfoAvailable_r16__Type =
| UE_MeasurementsAvailable_r16__connEstFailInfoAvailable_r16__true

val uE_MeasurementsAvailable_r16__connEstFailInfoAvailable_r16__nat__Format :
  int t_Format

val uE_MeasurementsAvailable_r16__connEstFailInfoAvailable_r16__F1 :
  uE_MeasurementsAvailable_r16__connEstFailInfoAvailable_r16__Type -> int

val uE_MeasurementsAvailable_r16__connEstFailInfoAvailable_r16__F2 :
  int -> uE_MeasurementsAvailable_r16__connEstFailInfoAvailable_r16__Type

type uE_MeasurementsAvailable_r16__rlf_InfoAvailable_r16__Type =
| UE_MeasurementsAvailable_r16__rlf_InfoAvailable_r16__true

val uE_MeasurementsAvailable_r16__rlf_InfoAvailable_r16__nat__Format :
  int t_Format

val uE_MeasurementsAvailable_r16__rlf_InfoAvailable_r16__F1 :
  uE_MeasurementsAvailable_r16__rlf_InfoAvailable_r16__Type -> int

val uE_MeasurementsAvailable_r16__rlf_InfoAvailable_r16__F2 :
  int -> uE_MeasurementsAvailable_r16__rlf_InfoAvailable_r16__Type

type uE_MeasurementsAvailable_r16__ext0O__successHO_InfoAvailable_r17__Type =
| UE_MeasurementsAvailable_r16__ext0O__successHO_InfoAvailable_r17__true

val uE_MeasurementsAvailable_r16__ext0O__successHO_InfoAvailable_r17__nat__Format :
  int t_Format

val uE_MeasurementsAvailable_r16__ext0O__successHO_InfoAvailable_r17__F1 :
  uE_MeasurementsAvailable_r16__ext0O__successHO_InfoAvailable_r17__Type -> int

val uE_MeasurementsAvailable_r16__ext0O__successHO_InfoAvailable_r17__F2 :
  int -> uE_MeasurementsAvailable_r16__ext0O__successHO_InfoAvailable_r17__Type

type uE_MeasurementsAvailable_r16__ext0O__Type = { uE_MeasurementsAvailable_r16__ext0O__successHO_InfoAvailable_r17 : 
                                                   uE_MeasurementsAvailable_r16__ext0O__successHO_InfoAvailable_r17__Type
                                                   option;
                                                   uE_MeasurementsAvailable_r16__ext0O__sigLogMeasConfigAvailable_r17 : 
                                                   bool option }

val uE_MeasurementsAvailable_r16__ext0O__list : seq_elem list

type uE_MeasurementsAvailable_r16__ext0__Type =
  uE_MeasurementsAvailable_r16__ext0O__Type

type uE_MeasurementsAvailable_r16__Type = { uE_MeasurementsAvailable_r16__logMeasAvailable_r16 : 
                                            uE_MeasurementsAvailable_r16__logMeasAvailable_r16__Type
                                            option;
                                            uE_MeasurementsAvailable_r16__logMeasAvailableBT_r16 : 
                                            uE_MeasurementsAvailable_r16__logMeasAvailableBT_r16__Type
                                            option;
                                            uE_MeasurementsAvailable_r16__logMeasAvailableWLAN_r16 : 
                                            uE_MeasurementsAvailable_r16__logMeasAvailableWLAN_r16__Type
                                            option;
                                            uE_MeasurementsAvailable_r16__connEstFailInfoAvailable_r16 : 
                                            uE_MeasurementsAvailable_r16__connEstFailInfoAvailable_r16__Type
                                            option;
                                            uE_MeasurementsAvailable_r16__rlf_InfoAvailable_r16 : 
                                            uE_MeasurementsAvailable_r16__rlf_InfoAvailable_r16__Type
                                            option;
                                            uE_MeasurementsAvailable_r16__ext0 : 
                                            uE_MeasurementsAvailable_r16__ext0__Type
                                            option }

val uE_MeasurementsAvailable_r16__root_list : seq_elem list

val uE_MeasurementsAvailable_r16__ext_list : typ list

val uE_MeasurementsAvailable_r16__logMeasAvailable_r16__Format :
  uE_MeasurementsAvailable_r16__logMeasAvailable_r16__Type t_Format

val uE_MeasurementsAvailable_r16__logMeasAvailableBT_r16__Format :
  uE_MeasurementsAvailable_r16__logMeasAvailableBT_r16__Type t_Format

val uE_MeasurementsAvailable_r16__logMeasAvailableWLAN_r16__Format :
  uE_MeasurementsAvailable_r16__logMeasAvailableWLAN_r16__Type t_Format

val uE_MeasurementsAvailable_r16__connEstFailInfoAvailable_r16__Format :
  uE_MeasurementsAvailable_r16__connEstFailInfoAvailable_r16__Type t_Format

val uE_MeasurementsAvailable_r16__rlf_InfoAvailable_r16__Format :
  uE_MeasurementsAvailable_r16__rlf_InfoAvailable_r16__Type t_Format

val uE_MeasurementsAvailable_r16__ext0O__successHO_InfoAvailable_r17__Format :
  uE_MeasurementsAvailable_r16__ext0O__successHO_InfoAvailable_r17__Type
  t_Format

type uE_MeasurementsAvailable_r16__ext0O__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val uE_MeasurementsAvailable_r16__ext0O__Format_list :
  uE_MeasurementsAvailable_r16__ext0O__Format_Type

val uE_MeasurementsAvailable_r16__ext0O__list__Format : seq_type t_Format

val uE_MeasurementsAvailable_r16__ext0O__F1 :
  uE_MeasurementsAvailable_r16__ext0O__Type ->
  uE_MeasurementsAvailable_r16__ext0O__successHO_InfoAvailable_r17__Type
  option * (bool option * unit)

val uE_MeasurementsAvailable_r16__ext0O__F2 :
  seq_type -> uE_MeasurementsAvailable_r16__ext0O__Type

val uE_MeasurementsAvailable_r16__ext0O__Format :
  uE_MeasurementsAvailable_r16__ext0O__Type t_Format

val uE_MeasurementsAvailable_r16__ext0__check_all_none :
  uE_MeasurementsAvailable_r16__ext0O__Type -> bool

val uE_MeasurementsAvailable_r16__ext0__Format :
  uE_MeasurementsAvailable_r16__ext0__Type t_Format

type uE_MeasurementsAvailable_r16__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))))

val uE_MeasurementsAvailable_r16__root_Format_list :
  uE_MeasurementsAvailable_r16__root_Format_Type

type uE_MeasurementsAvailable_r16__ext_Format_Type =
  uE_MeasurementsAvailable_r16__ext0__Type t_Format * unit t_Format

val uE_MeasurementsAvailable_r16__ext_Format_list :
  uE_MeasurementsAvailable_r16__ext_Format_Type

type uE_MeasurementsAvailable_r16__list_type = seq_type * seq_ext_type

val uE_MeasurementsAvailable_r16__list_format :
  uE_MeasurementsAvailable_r16__list_type t_Format

val uE_MeasurementsAvailable_r16__F1 :
  uE_MeasurementsAvailable_r16__Type -> uE_MeasurementsAvailable_r16__list_type

val uE_MeasurementsAvailable_r16__F2 :
  uE_MeasurementsAvailable_r16__list_type -> uE_MeasurementsAvailable_r16__Type

val uE_MeasurementsAvailable_r16__Format :
  uE_MeasurementsAvailable_r16__Type t_Format

type needForGapsIntraFreq_r16__gapIndicationIntra_r16__Type =
| NeedForGapsIntraFreq_r16__gapIndicationIntra_r16__gap
| NeedForGapsIntraFreq_r16__gapIndicationIntra_r16__no_gap

val needForGapsIntraFreq_r16__gapIndicationIntra_r16__nat__Format :
  int t_Format

val needForGapsIntraFreq_r16__gapIndicationIntra_r16__F1 :
  needForGapsIntraFreq_r16__gapIndicationIntra_r16__Type -> int

val needForGapsIntraFreq_r16__gapIndicationIntra_r16__F2 :
  int -> needForGapsIntraFreq_r16__gapIndicationIntra_r16__Type

type needForGapsIntraFreq_r16__Type = { needForGapsIntraFreq_r16__servCellId_r16 : 
                                        servCellIndex__Type;
                                        needForGapsIntraFreq_r16__gapIndicationIntra_r16 : 
                                        needForGapsIntraFreq_r16__gapIndicationIntra_r16__Type }

val needForGapsIntraFreq_r16__list : seq_elem list

val needForGapsIntraFreq_r16__gapIndicationIntra_r16__Format :
  needForGapsIntraFreq_r16__gapIndicationIntra_r16__Type t_Format

type needForGapsIntraFreq_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val needForGapsIntraFreq_r16__Format_list :
  needForGapsIntraFreq_r16__Format_Type

val needForGapsIntraFreq_r16__list__Format : seq_type t_Format

val needForGapsIntraFreq_r16__F1 :
  needForGapsIntraFreq_r16__Type ->
  servCellIndex__Type * (needForGapsIntraFreq_r16__gapIndicationIntra_r16__Type * unit)

val needForGapsIntraFreq_r16__F2 : seq_type -> needForGapsIntraFreq_r16__Type

val needForGapsIntraFreq_r16__Format : needForGapsIntraFreq_r16__Type t_Format

type needForGapsIntraFreqList_r16__Type = needForGapsIntraFreq_r16__Type list

val needForGapsIntraFreqList_r16__Format :
  needForGapsIntraFreqList_r16__Type t_Format

type needForGapsNR_r16__gapIndication_r16__Type =
| NeedForGapsNR_r16__gapIndication_r16__gap
| NeedForGapsNR_r16__gapIndication_r16__no_gap

val needForGapsNR_r16__gapIndication_r16__nat__Format : int t_Format

val needForGapsNR_r16__gapIndication_r16__F1 :
  needForGapsNR_r16__gapIndication_r16__Type -> int

val needForGapsNR_r16__gapIndication_r16__F2 :
  int -> needForGapsNR_r16__gapIndication_r16__Type

type needForGapsNR_r16__Type = { needForGapsNR_r16__bandNR_r16 : freqBandIndicatorNR__Type;
                                 needForGapsNR_r16__gapIndication_r16 : 
                                 needForGapsNR_r16__gapIndication_r16__Type }

val needForGapsNR_r16__list : seq_elem list

val needForGapsNR_r16__gapIndication_r16__Format :
  needForGapsNR_r16__gapIndication_r16__Type t_Format

type needForGapsNR_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val needForGapsNR_r16__Format_list : needForGapsNR_r16__Format_Type

val needForGapsNR_r16__list__Format : seq_type t_Format

val needForGapsNR_r16__F1 :
  needForGapsNR_r16__Type ->
  freqBandIndicatorNR__Type * (needForGapsNR_r16__gapIndication_r16__Type * unit)

val needForGapsNR_r16__F2 : seq_type -> needForGapsNR_r16__Type

val needForGapsNR_r16__Format : needForGapsNR_r16__Type t_Format

type needForGapsBandListNR_r16__Type = needForGapsNR_r16__Type list

val needForGapsBandListNR_r16__Format :
  needForGapsBandListNR_r16__Type t_Format

type needForGapsInfoNR_r16__Type = { needForGapsInfoNR_r16__intraFreq_needForGap_r16 : 
                                     needForGapsIntraFreqList_r16__Type;
                                     needForGapsInfoNR_r16__interFreq_needForGap_r16 : 
                                     needForGapsBandListNR_r16__Type }

val needForGapsInfoNR_r16__list : seq_elem list

type needForGapsInfoNR_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val needForGapsInfoNR_r16__Format_list : needForGapsInfoNR_r16__Format_Type

val needForGapsInfoNR_r16__list__Format : seq_type t_Format

val needForGapsInfoNR_r16__F1 :
  needForGapsInfoNR_r16__Type ->
  needForGapsIntraFreqList_r16__Type * (needForGapsBandListNR_r16__Type * unit)

val needForGapsInfoNR_r16__F2 : seq_type -> needForGapsInfoNR_r16__Type

val needForGapsInfoNR_r16__Format : needForGapsInfoNR_r16__Type t_Format

type uplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__Type =
| UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__deactivated

val uplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__nat__Format :
  int t_Format

val uplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__F1 :
  uplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__Type
  -> int

val uplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__F2 :
  int ->
  uplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__Type

type uplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__Type =
| UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__bwp_Id_r16 of 
   bWP_Id__Type
| UplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16 of 
   uplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__Type

type uplinkTxDirectCurrentCarrierInfo_r16__Type = { uplinkTxDirectCurrentCarrierInfo_r16__servCellIndex_r16 : 
                                                    servCellIndex__Type;
                                                    uplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16 : 
                                                    uplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__Type }

val uplinkTxDirectCurrentCarrierInfo_r16__list : seq_elem list

val uplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__Format :
  uplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__deactivatedCarrier_r16__Type
  t_Format

val uplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__list__Format :
  (int, __) sigT t_Format

val uplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__F1 :
  uplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__Type -> choice

val uplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__F2 :
  choice -> uplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__Type

val uplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__Format :
  uplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__Type t_Format

type uplinkTxDirectCurrentCarrierInfo_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val uplinkTxDirectCurrentCarrierInfo_r16__Format_list :
  uplinkTxDirectCurrentCarrierInfo_r16__Format_Type

val uplinkTxDirectCurrentCarrierInfo_r16__list__Format : seq_type t_Format

val uplinkTxDirectCurrentCarrierInfo_r16__F1 :
  uplinkTxDirectCurrentCarrierInfo_r16__Type ->
  servCellIndex__Type * (uplinkTxDirectCurrentCarrierInfo_r16__servCellInfo_r16__Type * unit)

val uplinkTxDirectCurrentCarrierInfo_r16__F2 :
  seq_type -> uplinkTxDirectCurrentCarrierInfo_r16__Type

val uplinkTxDirectCurrentCarrierInfo_r16__Format :
  uplinkTxDirectCurrentCarrierInfo_r16__Type t_Format

type uplinkTxDirectCurrentTwoCarrierInfo_r16__Type = { uplinkTxDirectCurrentTwoCarrierInfo_r16__referenceCarrierIndex_r16 : 
                                                       servCellIndex__Type;
                                                       uplinkTxDirectCurrentTwoCarrierInfo_r16__shift7dot5kHz_r16 : 
                                                       bool;
                                                       uplinkTxDirectCurrentTwoCarrierInfo_r16__txDirectCurrentLocation_r16 : 
                                                       int }

val uplinkTxDirectCurrentTwoCarrierInfo_r16__list : seq_elem list

val uplinkTxDirectCurrentTwoCarrierInfo_r16__txDirectCurrentLocation_r16__Format :
  int t_Format

type uplinkTxDirectCurrentTwoCarrierInfo_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val uplinkTxDirectCurrentTwoCarrierInfo_r16__Format_list :
  uplinkTxDirectCurrentTwoCarrierInfo_r16__Format_Type

val uplinkTxDirectCurrentTwoCarrierInfo_r16__list__Format : seq_type t_Format

val uplinkTxDirectCurrentTwoCarrierInfo_r16__F1 :
  uplinkTxDirectCurrentTwoCarrierInfo_r16__Type ->
  servCellIndex__Type * (bool * (int * unit))

val uplinkTxDirectCurrentTwoCarrierInfo_r16__F2 :
  seq_type -> uplinkTxDirectCurrentTwoCarrierInfo_r16__Type

val uplinkTxDirectCurrentTwoCarrierInfo_r16__Format :
  uplinkTxDirectCurrentTwoCarrierInfo_r16__Type t_Format

type uplinkTxDirectCurrentTwoCarrier_r16__Type = { uplinkTxDirectCurrentTwoCarrier_r16__carrierOneInfo_r16 : 
                                                   uplinkTxDirectCurrentCarrierInfo_r16__Type;
                                                   uplinkTxDirectCurrentTwoCarrier_r16__carrierTwoInfo_r16 : 
                                                   uplinkTxDirectCurrentCarrierInfo_r16__Type;
                                                   uplinkTxDirectCurrentTwoCarrier_r16__singlePA_TxDirectCurrent_r16 : 
                                                   uplinkTxDirectCurrentTwoCarrierInfo_r16__Type;
                                                   uplinkTxDirectCurrentTwoCarrier_r16__secondPA_TxDirectCurrent_r16 : 
                                                   uplinkTxDirectCurrentTwoCarrierInfo_r16__Type
                                                   option }

val uplinkTxDirectCurrentTwoCarrier_r16__list : seq_elem list

type uplinkTxDirectCurrentTwoCarrier_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

val uplinkTxDirectCurrentTwoCarrier_r16__Format_list :
  uplinkTxDirectCurrentTwoCarrier_r16__Format_Type

val uplinkTxDirectCurrentTwoCarrier_r16__list__Format : seq_type t_Format

val uplinkTxDirectCurrentTwoCarrier_r16__F1 :
  uplinkTxDirectCurrentTwoCarrier_r16__Type ->
  uplinkTxDirectCurrentCarrierInfo_r16__Type * (uplinkTxDirectCurrentCarrierInfo_r16__Type * (uplinkTxDirectCurrentTwoCarrierInfo_r16__Type * (uplinkTxDirectCurrentTwoCarrierInfo_r16__Type
  option * unit)))

val uplinkTxDirectCurrentTwoCarrier_r16__F2 :
  seq_type -> uplinkTxDirectCurrentTwoCarrier_r16__Type

val uplinkTxDirectCurrentTwoCarrier_r16__Format :
  uplinkTxDirectCurrentTwoCarrier_r16__Type t_Format

type uplinkTxDirectCurrentTwoCarrierList_r16__Type =
  uplinkTxDirectCurrentTwoCarrier_r16__Type list

val uplinkTxDirectCurrentTwoCarrierList_r16__Format :
  uplinkTxDirectCurrentTwoCarrierList_r16__Type t_Format

type needForNCSG_IntraFreq_r17__gapIndicationIntra_r17__Type =
| NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__gap
| NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__ncsg
| NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__nogap_noncsg

val needForNCSG_IntraFreq_r17__gapIndicationIntra_r17__nat__Format :
  int t_Format

val needForNCSG_IntraFreq_r17__gapIndicationIntra_r17__F1 :
  needForNCSG_IntraFreq_r17__gapIndicationIntra_r17__Type -> int

val needForNCSG_IntraFreq_r17__gapIndicationIntra_r17__F2 :
  int -> needForNCSG_IntraFreq_r17__gapIndicationIntra_r17__Type

type needForNCSG_IntraFreq_r17__Type = { needForNCSG_IntraFreq_r17__servCellId_r17 : 
                                         servCellIndex__Type;
                                         needForNCSG_IntraFreq_r17__gapIndicationIntra_r17 : 
                                         needForNCSG_IntraFreq_r17__gapIndicationIntra_r17__Type }

val needForNCSG_IntraFreq_r17__list : seq_elem list

val needForNCSG_IntraFreq_r17__gapIndicationIntra_r17__Format :
  needForNCSG_IntraFreq_r17__gapIndicationIntra_r17__Type t_Format

type needForNCSG_IntraFreq_r17__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val needForNCSG_IntraFreq_r17__Format_list :
  needForNCSG_IntraFreq_r17__Format_Type

val needForNCSG_IntraFreq_r17__list__Format : seq_type t_Format

val needForNCSG_IntraFreq_r17__F1 :
  needForNCSG_IntraFreq_r17__Type ->
  servCellIndex__Type * (needForNCSG_IntraFreq_r17__gapIndicationIntra_r17__Type * unit)

val needForNCSG_IntraFreq_r17__F2 : seq_type -> needForNCSG_IntraFreq_r17__Type

val needForNCSG_IntraFreq_r17__Format :
  needForNCSG_IntraFreq_r17__Type t_Format

type needForNCSG_IntraFreqList_r17__Type = needForNCSG_IntraFreq_r17__Type list

val needForNCSG_IntraFreqList_r17__Format :
  needForNCSG_IntraFreqList_r17__Type t_Format

type needForNCSG_NR_r17__gapIndication_r17__Type =
| NeedForNCSG_NR_r17__gapIndication_r17__gap
| NeedForNCSG_NR_r17__gapIndication_r17__ncsg
| NeedForNCSG_NR_r17__gapIndication_r17__nogap_noncsg

val needForNCSG_NR_r17__gapIndication_r17__nat__Format : int t_Format

val needForNCSG_NR_r17__gapIndication_r17__F1 :
  needForNCSG_NR_r17__gapIndication_r17__Type -> int

val needForNCSG_NR_r17__gapIndication_r17__F2 :
  int -> needForNCSG_NR_r17__gapIndication_r17__Type

type needForNCSG_NR_r17__Type = { needForNCSG_NR_r17__bandNR_r17 : freqBandIndicatorNR__Type;
                                  needForNCSG_NR_r17__gapIndication_r17 : 
                                  needForNCSG_NR_r17__gapIndication_r17__Type }

val needForNCSG_NR_r17__list : seq_elem list

val needForNCSG_NR_r17__gapIndication_r17__Format :
  needForNCSG_NR_r17__gapIndication_r17__Type t_Format

type needForNCSG_NR_r17__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val needForNCSG_NR_r17__Format_list : needForNCSG_NR_r17__Format_Type

val needForNCSG_NR_r17__list__Format : seq_type t_Format

val needForNCSG_NR_r17__F1 :
  needForNCSG_NR_r17__Type ->
  freqBandIndicatorNR__Type * (needForNCSG_NR_r17__gapIndication_r17__Type * unit)

val needForNCSG_NR_r17__F2 : seq_type -> needForNCSG_NR_r17__Type

val needForNCSG_NR_r17__Format : needForNCSG_NR_r17__Type t_Format

type needForNCSG_BandListNR_r17__Type = needForNCSG_NR_r17__Type list

val needForNCSG_BandListNR_r17__Format :
  needForNCSG_BandListNR_r17__Type t_Format

type needForGapNCSG_InfoNR_r17__Type = { needForGapNCSG_InfoNR_r17__intraFreq_needForNCSG_r17 : 
                                         needForNCSG_IntraFreqList_r17__Type;
                                         needForGapNCSG_InfoNR_r17__interFreq_needForNCSG_r17 : 
                                         needForNCSG_BandListNR_r17__Type }

val needForGapNCSG_InfoNR_r17__list : seq_elem list

type needForGapNCSG_InfoNR_r17__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val needForGapNCSG_InfoNR_r17__Format_list :
  needForGapNCSG_InfoNR_r17__Format_Type

val needForGapNCSG_InfoNR_r17__list__Format : seq_type t_Format

val needForGapNCSG_InfoNR_r17__F1 :
  needForGapNCSG_InfoNR_r17__Type ->
  needForNCSG_IntraFreqList_r17__Type * (needForNCSG_BandListNR_r17__Type * unit)

val needForGapNCSG_InfoNR_r17__F2 : seq_type -> needForGapNCSG_InfoNR_r17__Type

val needForGapNCSG_InfoNR_r17__Format :
  needForGapNCSG_InfoNR_r17__Type t_Format

type needForNCSG_EUTRA_r17__gapIndication_r17__Type =
| NeedForNCSG_EUTRA_r17__gapIndication_r17__gap
| NeedForNCSG_EUTRA_r17__gapIndication_r17__ncsg
| NeedForNCSG_EUTRA_r17__gapIndication_r17__nogap_noncsg

val needForNCSG_EUTRA_r17__gapIndication_r17__nat__Format : int t_Format

val needForNCSG_EUTRA_r17__gapIndication_r17__F1 :
  needForNCSG_EUTRA_r17__gapIndication_r17__Type -> int

val needForNCSG_EUTRA_r17__gapIndication_r17__F2 :
  int -> needForNCSG_EUTRA_r17__gapIndication_r17__Type

type needForNCSG_EUTRA_r17__Type = { needForNCSG_EUTRA_r17__bandEUTRA_r17 : 
                                     freqBandIndicatorEUTRA__Type;
                                     needForNCSG_EUTRA_r17__gapIndication_r17 : 
                                     needForNCSG_EUTRA_r17__gapIndication_r17__Type }

val needForNCSG_EUTRA_r17__list : seq_elem list

val needForNCSG_EUTRA_r17__gapIndication_r17__Format :
  needForNCSG_EUTRA_r17__gapIndication_r17__Type t_Format

type needForNCSG_EUTRA_r17__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val needForNCSG_EUTRA_r17__Format_list : needForNCSG_EUTRA_r17__Format_Type

val needForNCSG_EUTRA_r17__list__Format : seq_type t_Format

val needForNCSG_EUTRA_r17__F1 :
  needForNCSG_EUTRA_r17__Type ->
  freqBandIndicatorEUTRA__Type * (needForNCSG_EUTRA_r17__gapIndication_r17__Type * unit)

val needForNCSG_EUTRA_r17__F2 : seq_type -> needForNCSG_EUTRA_r17__Type

val needForNCSG_EUTRA_r17__Format : needForNCSG_EUTRA_r17__Type t_Format

type needForGapNCSG_InfoEUTRA_r17__needForNCSG_EUTRA_r17__Type =
  needForNCSG_EUTRA_r17__Type list

type needForGapNCSG_InfoEUTRA_r17__Type = { needForGapNCSG_InfoEUTRA_r17__needForNCSG_EUTRA_r17 : 
                                            needForGapNCSG_InfoEUTRA_r17__needForNCSG_EUTRA_r17__Type }

val needForGapNCSG_InfoEUTRA_r17__list : seq_elem list

val needForGapNCSG_InfoEUTRA_r17__needForNCSG_EUTRA_r17__Format :
  needForGapNCSG_InfoEUTRA_r17__needForNCSG_EUTRA_r17__Type t_Format

type needForGapNCSG_InfoEUTRA_r17__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val needForGapNCSG_InfoEUTRA_r17__Format_list :
  needForGapNCSG_InfoEUTRA_r17__Format_Type

val needForGapNCSG_InfoEUTRA_r17__list__Format : seq_type t_Format

val needForGapNCSG_InfoEUTRA_r17__F1 :
  needForGapNCSG_InfoEUTRA_r17__Type ->
  needForGapNCSG_InfoEUTRA_r17__needForNCSG_EUTRA_r17__Type * unit

val needForGapNCSG_InfoEUTRA_r17__F2 :
  seq_type -> needForGapNCSG_InfoEUTRA_r17__Type

val needForGapNCSG_InfoEUTRA_r17__Format :
  needForGapNCSG_InfoEUTRA_r17__Type t_Format

type condReconfigId_r16__Type = int

val condReconfigId_r16__Format : int t_Format

type frequencyComponent_r17__Type =
| FrequencyComponent_r17__activeCarrier
| FrequencyComponent_r17__configuredCarrier
| FrequencyComponent_r17__activeBWP
| FrequencyComponent_r17__configuredBWP

val frequencyComponent_r17__nat__Format : int t_Format

val frequencyComponent_r17__F1 : frequencyComponent_r17__Type -> int

val frequencyComponent_r17__F2 : int -> frequencyComponent_r17__Type

val frequencyComponent_r17__Format : frequencyComponent_r17__Type t_Format

type defaultDC_Location_r17__Type =
| DefaultDC_Location_r17__ul of frequencyComponent_r17__Type
| DefaultDC_Location_r17__dl of frequencyComponent_r17__Type
| DefaultDC_Location_r17__ulAndDL of frequencyComponent_r17__Type

val defaultDC_Location_r17__list__Format : (int, __) sigT t_Format

val defaultDC_Location_r17__F1 : defaultDC_Location_r17__Type -> choice

val defaultDC_Location_r17__F2 : choice -> defaultDC_Location_r17__Type

val defaultDC_Location_r17__Format : defaultDC_Location_r17__Type t_Format

type offsetValue_r17__Type = { offsetValue_r17__offsetValue_r17 : int;
                               offsetValue_r17__shift7dot5kHz_r17 : bool }

val offsetValue_r17__list : seq_elem list

val offsetValue_r17__offsetValue_r17__Format : int t_Format

type offsetValue_r17__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val offsetValue_r17__Format_list : offsetValue_r17__Format_Type

val offsetValue_r17__list__Format : seq_type t_Format

val offsetValue_r17__F1 : offsetValue_r17__Type -> int * (bool * unit)

val offsetValue_r17__F2 : seq_type -> offsetValue_r17__Type

val offsetValue_r17__Format : offsetValue_r17__Type t_Format

type cC_Group_r17__offsetToDefault_r17__offsetlist__Type =
  offsetValue_r17__Type list

type cC_Group_r17__offsetToDefault_r17__Type =
| CC_Group_r17__offsetToDefault_r17__offsetValue of offsetValue_r17__Type
| CC_Group_r17__offsetToDefault_r17__offsetlist of cC_Group_r17__offsetToDefault_r17__offsetlist__Type

type cC_Group_r17__Type = { cC_Group_r17__servCellIndexLower_r17 : servCellIndex__Type;
                            cC_Group_r17__servCellIndexHigher_r17 : servCellIndex__Type
                                                                    option;
                            cC_Group_r17__defaultDC_Location_r17 : defaultDC_Location_r17__Type;
                            cC_Group_r17__offsetToDefault_r17 : cC_Group_r17__offsetToDefault_r17__Type
                                                                option }

val cC_Group_r17__list : seq_elem list

val cC_Group_r17__offsetToDefault_r17__offsetlist__Format :
  cC_Group_r17__offsetToDefault_r17__offsetlist__Type t_Format

val cC_Group_r17__offsetToDefault_r17__list__Format : (int, __) sigT t_Format

val cC_Group_r17__offsetToDefault_r17__F1 :
  cC_Group_r17__offsetToDefault_r17__Type -> choice

val cC_Group_r17__offsetToDefault_r17__F2 :
  choice -> cC_Group_r17__offsetToDefault_r17__Type

val cC_Group_r17__offsetToDefault_r17__Format :
  cC_Group_r17__offsetToDefault_r17__Type t_Format

type cC_Group_r17__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

val cC_Group_r17__Format_list : cC_Group_r17__Format_Type

val cC_Group_r17__list__Format : seq_type t_Format

val cC_Group_r17__F1 :
  cC_Group_r17__Type -> servCellIndex__Type * (servCellIndex__Type
  option * (defaultDC_Location_r17__Type * (cC_Group_r17__offsetToDefault_r17__Type
  option * unit)))

val cC_Group_r17__F2 : seq_type -> cC_Group_r17__Type

val cC_Group_r17__Format : cC_Group_r17__Type t_Format

type uplinkTxDirectCurrentMoreCarrierList_r17__Type = cC_Group_r17__Type list

val uplinkTxDirectCurrentMoreCarrierList_r17__Format :
  uplinkTxDirectCurrentMoreCarrierList_r17__Type t_Format

type rRCReconfigurationComplete_v1720_IEs__nonCriticalExtension__Type =
| Make__RRCReconfigurationComplete_v1720_IEs__nonCriticalExtension__Type

type rRCReconfigurationComplete_v1720_IEs__Type = { rRCReconfigurationComplete_v1720_IEs__uplinkTxDirectCurrentMoreCarrierList_r17 : 
                                                    uplinkTxDirectCurrentMoreCarrierList_r17__Type
                                                    option;
                                                    rRCReconfigurationComplete_v1720_IEs__nonCriticalExtension : 
                                                    rRCReconfigurationComplete_v1720_IEs__nonCriticalExtension__Type
                                                    option }

val rRCReconfigurationComplete_v1720_IEs__list : seq_elem list

val rRCReconfigurationComplete_v1720_IEs__nonCriticalExtension__Format :
  rRCReconfigurationComplete_v1720_IEs__nonCriticalExtension__Type t_Format

type rRCReconfigurationComplete_v1720_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val rRCReconfigurationComplete_v1720_IEs__Format_list :
  rRCReconfigurationComplete_v1720_IEs__Format_Type

val rRCReconfigurationComplete_v1720_IEs__list__Format : seq_type t_Format

val rRCReconfigurationComplete_v1720_IEs__F1 :
  rRCReconfigurationComplete_v1720_IEs__Type ->
  uplinkTxDirectCurrentMoreCarrierList_r17__Type
  option * (rRCReconfigurationComplete_v1720_IEs__nonCriticalExtension__Type
  option * unit)

val rRCReconfigurationComplete_v1720_IEs__F2 :
  seq_type -> rRCReconfigurationComplete_v1720_IEs__Type

val rRCReconfigurationComplete_v1720_IEs__Format :
  rRCReconfigurationComplete_v1720_IEs__Type t_Format

type rRCReconfigurationComplete_v1700_IEs__Type = { rRCReconfigurationComplete_v1700_IEs__needForGapNCSG_InfoNR_r17 : 
                                                    needForGapNCSG_InfoNR_r17__Type
                                                    option;
                                                    rRCReconfigurationComplete_v1700_IEs__needForGapNCSG_InfoEUTRA_r17 : 
                                                    needForGapNCSG_InfoEUTRA_r17__Type
                                                    option;
                                                    rRCReconfigurationComplete_v1700_IEs__selectedCondRRCReconfig_r17 : 
                                                    condReconfigId_r16__Type
                                                    option;
                                                    rRCReconfigurationComplete_v1700_IEs__nonCriticalExtension : 
                                                    rRCReconfigurationComplete_v1720_IEs__Type
                                                    option }

val rRCReconfigurationComplete_v1700_IEs__list : seq_elem list

type rRCReconfigurationComplete_v1700_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

val rRCReconfigurationComplete_v1700_IEs__Format_list :
  rRCReconfigurationComplete_v1700_IEs__Format_Type

val rRCReconfigurationComplete_v1700_IEs__list__Format : seq_type t_Format

val rRCReconfigurationComplete_v1700_IEs__F1 :
  rRCReconfigurationComplete_v1700_IEs__Type ->
  needForGapNCSG_InfoNR_r17__Type option * (needForGapNCSG_InfoEUTRA_r17__Type
  option * (condReconfigId_r16__Type
  option * (rRCReconfigurationComplete_v1720_IEs__Type option * unit)))

val rRCReconfigurationComplete_v1700_IEs__F2 :
  seq_type -> rRCReconfigurationComplete_v1700_IEs__Type

val rRCReconfigurationComplete_v1700_IEs__Format :
  rRCReconfigurationComplete_v1700_IEs__Type t_Format

type rRCReconfigurationComplete_v1640_IEs__Type = { rRCReconfigurationComplete_v1640_IEs__uplinkTxDirectCurrentTwoCarrierList_r16 : 
                                                    uplinkTxDirectCurrentTwoCarrierList_r16__Type
                                                    option;
                                                    rRCReconfigurationComplete_v1640_IEs__nonCriticalExtension : 
                                                    rRCReconfigurationComplete_v1700_IEs__Type
                                                    option }

val rRCReconfigurationComplete_v1640_IEs__list : seq_elem list

type rRCReconfigurationComplete_v1640_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val rRCReconfigurationComplete_v1640_IEs__Format_list :
  rRCReconfigurationComplete_v1640_IEs__Format_Type

val rRCReconfigurationComplete_v1640_IEs__list__Format : seq_type t_Format

val rRCReconfigurationComplete_v1640_IEs__F1 :
  rRCReconfigurationComplete_v1640_IEs__Type ->
  uplinkTxDirectCurrentTwoCarrierList_r16__Type
  option * (rRCReconfigurationComplete_v1700_IEs__Type option * unit)

val rRCReconfigurationComplete_v1640_IEs__F2 :
  seq_type -> rRCReconfigurationComplete_v1640_IEs__Type

val rRCReconfigurationComplete_v1640_IEs__Format :
  rRCReconfigurationComplete_v1640_IEs__Type t_Format

type rRCReconfigurationComplete_v1610_IEs__Type = { rRCReconfigurationComplete_v1610_IEs__ue_MeasurementsAvailable_r16 : 
                                                    uE_MeasurementsAvailable_r16__Type
                                                    option;
                                                    rRCReconfigurationComplete_v1610_IEs__needForGapsInfoNR_r16 : 
                                                    needForGapsInfoNR_r16__Type
                                                    option;
                                                    rRCReconfigurationComplete_v1610_IEs__nonCriticalExtension : 
                                                    rRCReconfigurationComplete_v1640_IEs__Type
                                                    option }

val rRCReconfigurationComplete_v1610_IEs__list : seq_elem list

type rRCReconfigurationComplete_v1610_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val rRCReconfigurationComplete_v1610_IEs__Format_list :
  rRCReconfigurationComplete_v1610_IEs__Format_Type

val rRCReconfigurationComplete_v1610_IEs__list__Format : seq_type t_Format

val rRCReconfigurationComplete_v1610_IEs__F1 :
  rRCReconfigurationComplete_v1610_IEs__Type ->
  uE_MeasurementsAvailable_r16__Type option * (needForGapsInfoNR_r16__Type
  option * (rRCReconfigurationComplete_v1640_IEs__Type option * unit))

val rRCReconfigurationComplete_v1610_IEs__F2 :
  seq_type -> rRCReconfigurationComplete_v1610_IEs__Type

val rRCReconfigurationComplete_v1610_IEs__Format :
  rRCReconfigurationComplete_v1610_IEs__Type t_Format

type rRCReconfigurationComplete_v1560_IEs__scg_Response__Type =
| RRCReconfigurationComplete_v1560_IEs__scg_Response__nr_SCG_Response of 
   octet_string
| RRCReconfigurationComplete_v1560_IEs__scg_Response__eutra_SCG_Response of 
   octet_string

type rRCReconfigurationComplete_v1560_IEs__Type = { rRCReconfigurationComplete_v1560_IEs__scg_Response : 
                                                    rRCReconfigurationComplete_v1560_IEs__scg_Response__Type
                                                    option;
                                                    rRCReconfigurationComplete_v1560_IEs__nonCriticalExtension : 
                                                    rRCReconfigurationComplete_v1610_IEs__Type
                                                    option }

val rRCReconfigurationComplete_v1560_IEs__list : seq_elem list

val rRCReconfigurationComplete_v1560_IEs__scg_Response__list__Format :
  (int, __) sigT t_Format

val rRCReconfigurationComplete_v1560_IEs__scg_Response__F1 :
  rRCReconfigurationComplete_v1560_IEs__scg_Response__Type -> choice

val rRCReconfigurationComplete_v1560_IEs__scg_Response__F2 :
  choice -> rRCReconfigurationComplete_v1560_IEs__scg_Response__Type

val rRCReconfigurationComplete_v1560_IEs__scg_Response__Format :
  rRCReconfigurationComplete_v1560_IEs__scg_Response__Type t_Format

type rRCReconfigurationComplete_v1560_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val rRCReconfigurationComplete_v1560_IEs__Format_list :
  rRCReconfigurationComplete_v1560_IEs__Format_Type

val rRCReconfigurationComplete_v1560_IEs__list__Format : seq_type t_Format

val rRCReconfigurationComplete_v1560_IEs__F1 :
  rRCReconfigurationComplete_v1560_IEs__Type ->
  rRCReconfigurationComplete_v1560_IEs__scg_Response__Type
  option * (rRCReconfigurationComplete_v1610_IEs__Type option * unit)

val rRCReconfigurationComplete_v1560_IEs__F2 :
  seq_type -> rRCReconfigurationComplete_v1560_IEs__Type

val rRCReconfigurationComplete_v1560_IEs__Format :
  rRCReconfigurationComplete_v1560_IEs__Type t_Format

type rRCReconfigurationComplete_v1530_IEs__Type = { rRCReconfigurationComplete_v1530_IEs__uplinkTxDirectCurrentList : 
                                                    uplinkTxDirectCurrentList__Type
                                                    option;
                                                    rRCReconfigurationComplete_v1530_IEs__nonCriticalExtension : 
                                                    rRCReconfigurationComplete_v1560_IEs__Type
                                                    option }

val rRCReconfigurationComplete_v1530_IEs__list : seq_elem list

type rRCReconfigurationComplete_v1530_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val rRCReconfigurationComplete_v1530_IEs__Format_list :
  rRCReconfigurationComplete_v1530_IEs__Format_Type

val rRCReconfigurationComplete_v1530_IEs__list__Format : seq_type t_Format

val rRCReconfigurationComplete_v1530_IEs__F1 :
  rRCReconfigurationComplete_v1530_IEs__Type ->
  uplinkTxDirectCurrentList__Type
  option * (rRCReconfigurationComplete_v1560_IEs__Type option * unit)

val rRCReconfigurationComplete_v1530_IEs__F2 :
  seq_type -> rRCReconfigurationComplete_v1530_IEs__Type

val rRCReconfigurationComplete_v1530_IEs__Format :
  rRCReconfigurationComplete_v1530_IEs__Type t_Format

type rRCReconfigurationComplete_IEs__Type = { rRCReconfigurationComplete_IEs__lateNonCriticalExtension : 
                                              octet_string option;
                                              rRCReconfigurationComplete_IEs__nonCriticalExtension : 
                                              rRCReconfigurationComplete_v1530_IEs__Type
                                              option }

val rRCReconfigurationComplete_IEs__list : seq_elem list

type rRCReconfigurationComplete_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val rRCReconfigurationComplete_IEs__Format_list :
  rRCReconfigurationComplete_IEs__Format_Type

val rRCReconfigurationComplete_IEs__list__Format : seq_type t_Format

val rRCReconfigurationComplete_IEs__F1 :
  rRCReconfigurationComplete_IEs__Type -> octet_string
  option * (rRCReconfigurationComplete_v1530_IEs__Type option * unit)

val rRCReconfigurationComplete_IEs__F2 :
  seq_type -> rRCReconfigurationComplete_IEs__Type

val rRCReconfigurationComplete_IEs__Format :
  rRCReconfigurationComplete_IEs__Type t_Format

type rRCReconfigurationComplete__criticalExtensions__criticalExtensionsFuture__Type =
| Make__RRCReconfigurationComplete__criticalExtensions__criticalExtensionsFuture__Type

type rRCReconfigurationComplete__criticalExtensions__Type =
| RRCReconfigurationComplete__criticalExtensions__rrcReconfigurationComplete of 
   rRCReconfigurationComplete_IEs__Type
| RRCReconfigurationComplete__criticalExtensions__criticalExtensionsFuture of 
   rRCReconfigurationComplete__criticalExtensions__criticalExtensionsFuture__Type

type rRCReconfigurationComplete__Type = { rRCReconfigurationComplete__rrc_TransactionIdentifier : 
                                          rRC_TransactionIdentifier__Type;
                                          rRCReconfigurationComplete__criticalExtensions : 
                                          rRCReconfigurationComplete__criticalExtensions__Type }

val rRCReconfigurationComplete__list : seq_elem list

val rRCReconfigurationComplete__criticalExtensions__criticalExtensionsFuture__Format :
  rRCReconfigurationComplete__criticalExtensions__criticalExtensionsFuture__Type
  t_Format

val rRCReconfigurationComplete__criticalExtensions__list__Format :
  (int, __) sigT t_Format

val rRCReconfigurationComplete__criticalExtensions__F1 :
  rRCReconfigurationComplete__criticalExtensions__Type -> choice

val rRCReconfigurationComplete__criticalExtensions__F2 :
  choice -> rRCReconfigurationComplete__criticalExtensions__Type

val rRCReconfigurationComplete__criticalExtensions__Format :
  rRCReconfigurationComplete__criticalExtensions__Type t_Format

type rRCReconfigurationComplete__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val rRCReconfigurationComplete__Format_list :
  rRCReconfigurationComplete__Format_Type

val rRCReconfigurationComplete__list__Format : seq_type t_Format

val rRCReconfigurationComplete__F1 :
  rRCReconfigurationComplete__Type ->
  rRC_TransactionIdentifier__Type * (rRCReconfigurationComplete__criticalExtensions__Type * unit)

val rRCReconfigurationComplete__F2 :
  seq_type -> rRCReconfigurationComplete__Type

val rRCReconfigurationComplete__Format :
  rRCReconfigurationComplete__Type t_Format

type aMF_Identifier__Type = bit_string_fixed

val aMF_Identifier__Format : aMF_Identifier__Type t_Format

type registeredAMF__Type = { registeredAMF__plmn_Identity : pLMN_Identity__Type
                                                            option;
                             registeredAMF__amf_Identifier : aMF_Identifier__Type }

val registeredAMF__list : seq_elem list

type registeredAMF__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val registeredAMF__Format_list : registeredAMF__Format_Type

val registeredAMF__list__Format : seq_type t_Format

val registeredAMF__F1 :
  registeredAMF__Type -> pLMN_Identity__Type
  option * (aMF_Identifier__Type * unit)

val registeredAMF__F2 : seq_type -> registeredAMF__Type

val registeredAMF__Format : registeredAMF__Type t_Format

type s_NSSAI__sst__Type = bit_string_fixed

type s_NSSAI__sst_SD__Type = bit_string_fixed

type s_NSSAI__Type =
| S_NSSAI__sst of s_NSSAI__sst__Type
| S_NSSAI__sst_SD of s_NSSAI__sst_SD__Type

val s_NSSAI__sst__Format : s_NSSAI__sst__Type t_Format

val s_NSSAI__sst_SD__Format : s_NSSAI__sst_SD__Type t_Format

val s_NSSAI__list__Format : (int, __) sigT t_Format

val s_NSSAI__F1 : s_NSSAI__Type -> choice

val s_NSSAI__F2 : choice -> s_NSSAI__Type

val s_NSSAI__Format : s_NSSAI__Type t_Format

type dedicatedNAS_Message__Type = octet_string

val dedicatedNAS_Message__Format : char list t_Format

type nG_5G_S_TMSI__Type = bit_string_fixed

val nG_5G_S_TMSI__Format : nG_5G_S_TMSI__Type t_Format

type rRCSetupComplete_v1700_IEs__onboardingRequest_r17__Type =
| RRCSetupComplete_v1700_IEs__onboardingRequest_r17__true

val rRCSetupComplete_v1700_IEs__onboardingRequest_r17__nat__Format :
  int t_Format

val rRCSetupComplete_v1700_IEs__onboardingRequest_r17__F1 :
  rRCSetupComplete_v1700_IEs__onboardingRequest_r17__Type -> int

val rRCSetupComplete_v1700_IEs__onboardingRequest_r17__F2 :
  int -> rRCSetupComplete_v1700_IEs__onboardingRequest_r17__Type

type rRCSetupComplete_v1700_IEs__nonCriticalExtension__Type =
| Make__RRCSetupComplete_v1700_IEs__nonCriticalExtension__Type

type rRCSetupComplete_v1700_IEs__Type = { rRCSetupComplete_v1700_IEs__onboardingRequest_r17 : 
                                          rRCSetupComplete_v1700_IEs__onboardingRequest_r17__Type
                                          option;
                                          rRCSetupComplete_v1700_IEs__nonCriticalExtension : 
                                          rRCSetupComplete_v1700_IEs__nonCriticalExtension__Type
                                          option }

val rRCSetupComplete_v1700_IEs__list : seq_elem list

val rRCSetupComplete_v1700_IEs__onboardingRequest_r17__Format :
  rRCSetupComplete_v1700_IEs__onboardingRequest_r17__Type t_Format

val rRCSetupComplete_v1700_IEs__nonCriticalExtension__Format :
  rRCSetupComplete_v1700_IEs__nonCriticalExtension__Type t_Format

type rRCSetupComplete_v1700_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val rRCSetupComplete_v1700_IEs__Format_list :
  rRCSetupComplete_v1700_IEs__Format_Type

val rRCSetupComplete_v1700_IEs__list__Format : seq_type t_Format

val rRCSetupComplete_v1700_IEs__F1 :
  rRCSetupComplete_v1700_IEs__Type ->
  rRCSetupComplete_v1700_IEs__onboardingRequest_r17__Type
  option * (rRCSetupComplete_v1700_IEs__nonCriticalExtension__Type
  option * unit)

val rRCSetupComplete_v1700_IEs__F2 :
  seq_type -> rRCSetupComplete_v1700_IEs__Type

val rRCSetupComplete_v1700_IEs__Format :
  rRCSetupComplete_v1700_IEs__Type t_Format

type rRCSetupComplete_v1690_IEs__ul_RRC_Segmentation_r16__Type =
| RRCSetupComplete_v1690_IEs__ul_RRC_Segmentation_r16__true

val rRCSetupComplete_v1690_IEs__ul_RRC_Segmentation_r16__nat__Format :
  int t_Format

val rRCSetupComplete_v1690_IEs__ul_RRC_Segmentation_r16__F1 :
  rRCSetupComplete_v1690_IEs__ul_RRC_Segmentation_r16__Type -> int

val rRCSetupComplete_v1690_IEs__ul_RRC_Segmentation_r16__F2 :
  int -> rRCSetupComplete_v1690_IEs__ul_RRC_Segmentation_r16__Type

type rRCSetupComplete_v1690_IEs__Type = { rRCSetupComplete_v1690_IEs__ul_RRC_Segmentation_r16 : 
                                          rRCSetupComplete_v1690_IEs__ul_RRC_Segmentation_r16__Type
                                          option;
                                          rRCSetupComplete_v1690_IEs__nonCriticalExtension : 
                                          rRCSetupComplete_v1700_IEs__Type
                                          option }

val rRCSetupComplete_v1690_IEs__list : seq_elem list

val rRCSetupComplete_v1690_IEs__ul_RRC_Segmentation_r16__Format :
  rRCSetupComplete_v1690_IEs__ul_RRC_Segmentation_r16__Type t_Format

type rRCSetupComplete_v1690_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val rRCSetupComplete_v1690_IEs__Format_list :
  rRCSetupComplete_v1690_IEs__Format_Type

val rRCSetupComplete_v1690_IEs__list__Format : seq_type t_Format

val rRCSetupComplete_v1690_IEs__F1 :
  rRCSetupComplete_v1690_IEs__Type ->
  rRCSetupComplete_v1690_IEs__ul_RRC_Segmentation_r16__Type
  option * (rRCSetupComplete_v1700_IEs__Type option * unit)

val rRCSetupComplete_v1690_IEs__F2 :
  seq_type -> rRCSetupComplete_v1690_IEs__Type

val rRCSetupComplete_v1690_IEs__Format :
  rRCSetupComplete_v1690_IEs__Type t_Format

type rRCSetupComplete_v1610_IEs__iab_NodeIndication_r16__Type =
| RRCSetupComplete_v1610_IEs__iab_NodeIndication_r16__true

val rRCSetupComplete_v1610_IEs__iab_NodeIndication_r16__nat__Format :
  int t_Format

val rRCSetupComplete_v1610_IEs__iab_NodeIndication_r16__F1 :
  rRCSetupComplete_v1610_IEs__iab_NodeIndication_r16__Type -> int

val rRCSetupComplete_v1610_IEs__iab_NodeIndication_r16__F2 :
  int -> rRCSetupComplete_v1610_IEs__iab_NodeIndication_r16__Type

type rRCSetupComplete_v1610_IEs__idleMeasAvailable_r16__Type =
| RRCSetupComplete_v1610_IEs__idleMeasAvailable_r16__true

val rRCSetupComplete_v1610_IEs__idleMeasAvailable_r16__nat__Format :
  int t_Format

val rRCSetupComplete_v1610_IEs__idleMeasAvailable_r16__F1 :
  rRCSetupComplete_v1610_IEs__idleMeasAvailable_r16__Type -> int

val rRCSetupComplete_v1610_IEs__idleMeasAvailable_r16__F2 :
  int -> rRCSetupComplete_v1610_IEs__idleMeasAvailable_r16__Type

type rRCSetupComplete_v1610_IEs__mobilityHistoryAvail_r16__Type =
| RRCSetupComplete_v1610_IEs__mobilityHistoryAvail_r16__true

val rRCSetupComplete_v1610_IEs__mobilityHistoryAvail_r16__nat__Format :
  int t_Format

val rRCSetupComplete_v1610_IEs__mobilityHistoryAvail_r16__F1 :
  rRCSetupComplete_v1610_IEs__mobilityHistoryAvail_r16__Type -> int

val rRCSetupComplete_v1610_IEs__mobilityHistoryAvail_r16__F2 :
  int -> rRCSetupComplete_v1610_IEs__mobilityHistoryAvail_r16__Type

type rRCSetupComplete_v1610_IEs__mobilityState_r16__Type =
| RRCSetupComplete_v1610_IEs__mobilityState_r16__normal
| RRCSetupComplete_v1610_IEs__mobilityState_r16__medium
| RRCSetupComplete_v1610_IEs__mobilityState_r16__high
| RRCSetupComplete_v1610_IEs__mobilityState_r16__spare

val rRCSetupComplete_v1610_IEs__mobilityState_r16__nat__Format : int t_Format

val rRCSetupComplete_v1610_IEs__mobilityState_r16__F1 :
  rRCSetupComplete_v1610_IEs__mobilityState_r16__Type -> int

val rRCSetupComplete_v1610_IEs__mobilityState_r16__F2 :
  int -> rRCSetupComplete_v1610_IEs__mobilityState_r16__Type

type rRCSetupComplete_v1610_IEs__Type = { rRCSetupComplete_v1610_IEs__iab_NodeIndication_r16 : 
                                          rRCSetupComplete_v1610_IEs__iab_NodeIndication_r16__Type
                                          option;
                                          rRCSetupComplete_v1610_IEs__idleMeasAvailable_r16 : 
                                          rRCSetupComplete_v1610_IEs__idleMeasAvailable_r16__Type
                                          option;
                                          rRCSetupComplete_v1610_IEs__ue_MeasurementsAvailable_r16 : 
                                          uE_MeasurementsAvailable_r16__Type
                                          option;
                                          rRCSetupComplete_v1610_IEs__mobilityHistoryAvail_r16 : 
                                          rRCSetupComplete_v1610_IEs__mobilityHistoryAvail_r16__Type
                                          option;
                                          rRCSetupComplete_v1610_IEs__mobilityState_r16 : 
                                          rRCSetupComplete_v1610_IEs__mobilityState_r16__Type
                                          option;
                                          rRCSetupComplete_v1610_IEs__nonCriticalExtension : 
                                          rRCSetupComplete_v1690_IEs__Type
                                          option }

val rRCSetupComplete_v1610_IEs__list : seq_elem list

val rRCSetupComplete_v1610_IEs__iab_NodeIndication_r16__Format :
  rRCSetupComplete_v1610_IEs__iab_NodeIndication_r16__Type t_Format

val rRCSetupComplete_v1610_IEs__idleMeasAvailable_r16__Format :
  rRCSetupComplete_v1610_IEs__idleMeasAvailable_r16__Type t_Format

val rRCSetupComplete_v1610_IEs__mobilityHistoryAvail_r16__Format :
  rRCSetupComplete_v1610_IEs__mobilityHistoryAvail_r16__Type t_Format

val rRCSetupComplete_v1610_IEs__mobilityState_r16__Format :
  rRCSetupComplete_v1610_IEs__mobilityState_r16__Type t_Format

type rRCSetupComplete_v1610_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))))

val rRCSetupComplete_v1610_IEs__Format_list :
  rRCSetupComplete_v1610_IEs__Format_Type

val rRCSetupComplete_v1610_IEs__list__Format : seq_type t_Format

val rRCSetupComplete_v1610_IEs__F1 :
  rRCSetupComplete_v1610_IEs__Type ->
  rRCSetupComplete_v1610_IEs__iab_NodeIndication_r16__Type
  option * (rRCSetupComplete_v1610_IEs__idleMeasAvailable_r16__Type
  option * (uE_MeasurementsAvailable_r16__Type
  option * (rRCSetupComplete_v1610_IEs__mobilityHistoryAvail_r16__Type
  option * (rRCSetupComplete_v1610_IEs__mobilityState_r16__Type
  option * (rRCSetupComplete_v1690_IEs__Type option * unit)))))

val rRCSetupComplete_v1610_IEs__F2 :
  seq_type -> rRCSetupComplete_v1610_IEs__Type

val rRCSetupComplete_v1610_IEs__Format :
  rRCSetupComplete_v1610_IEs__Type t_Format

type rRCSetupComplete_IEs__guami_Type__Type =
| RRCSetupComplete_IEs__guami_Type__native
| RRCSetupComplete_IEs__guami_Type__mapped

val rRCSetupComplete_IEs__guami_Type__nat__Format : int t_Format

val rRCSetupComplete_IEs__guami_Type__F1 :
  rRCSetupComplete_IEs__guami_Type__Type -> int

val rRCSetupComplete_IEs__guami_Type__F2 :
  int -> rRCSetupComplete_IEs__guami_Type__Type

type rRCSetupComplete_IEs__s_NSSAI_List__Type = s_NSSAI__Type list

type rRCSetupComplete_IEs__ng_5G_S_TMSI_Value__ng_5G_S_TMSI_Part2__Type =
  bit_string_fixed

type rRCSetupComplete_IEs__ng_5G_S_TMSI_Value__Type =
| RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__ng_5G_S_TMSI of nG_5G_S_TMSI__Type
| RRCSetupComplete_IEs__ng_5G_S_TMSI_Value__ng_5G_S_TMSI_Part2 of rRCSetupComplete_IEs__ng_5G_S_TMSI_Value__ng_5G_S_TMSI_Part2__Type

type rRCSetupComplete_IEs__Type = { rRCSetupComplete_IEs__selectedPLMN_Identity : 
                                    int;
                                    rRCSetupComplete_IEs__registeredAMF : 
                                    registeredAMF__Type option;
                                    rRCSetupComplete_IEs__guami_Type : 
                                    rRCSetupComplete_IEs__guami_Type__Type
                                    option;
                                    rRCSetupComplete_IEs__s_NSSAI_List : 
                                    rRCSetupComplete_IEs__s_NSSAI_List__Type
                                    option;
                                    rRCSetupComplete_IEs__dedicatedNAS_Message : 
                                    dedicatedNAS_Message__Type;
                                    rRCSetupComplete_IEs__ng_5G_S_TMSI_Value : 
                                    rRCSetupComplete_IEs__ng_5G_S_TMSI_Value__Type
                                    option;
                                    rRCSetupComplete_IEs__lateNonCriticalExtension : 
                                    octet_string option;
                                    rRCSetupComplete_IEs__nonCriticalExtension : 
                                    rRCSetupComplete_v1610_IEs__Type option }

val rRCSetupComplete_IEs__list : seq_elem list

val rRCSetupComplete_IEs__selectedPLMN_Identity__Format : int t_Format

val rRCSetupComplete_IEs__guami_Type__Format :
  rRCSetupComplete_IEs__guami_Type__Type t_Format

val rRCSetupComplete_IEs__s_NSSAI_List__Format :
  rRCSetupComplete_IEs__s_NSSAI_List__Type t_Format

val rRCSetupComplete_IEs__ng_5G_S_TMSI_Value__ng_5G_S_TMSI_Part2__Format :
  rRCSetupComplete_IEs__ng_5G_S_TMSI_Value__ng_5G_S_TMSI_Part2__Type t_Format

val rRCSetupComplete_IEs__ng_5G_S_TMSI_Value__list__Format :
  (int, __) sigT t_Format

val rRCSetupComplete_IEs__ng_5G_S_TMSI_Value__F1 :
  rRCSetupComplete_IEs__ng_5G_S_TMSI_Value__Type -> choice

val rRCSetupComplete_IEs__ng_5G_S_TMSI_Value__F2 :
  choice -> rRCSetupComplete_IEs__ng_5G_S_TMSI_Value__Type

val rRCSetupComplete_IEs__ng_5G_S_TMSI_Value__Format :
  rRCSetupComplete_IEs__ng_5G_S_TMSI_Value__Type t_Format

type rRCSetupComplete_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))))))

val rRCSetupComplete_IEs__Format_list : rRCSetupComplete_IEs__Format_Type

val rRCSetupComplete_IEs__list__Format : seq_type t_Format

val rRCSetupComplete_IEs__F1 :
  rRCSetupComplete_IEs__Type -> int * (registeredAMF__Type
  option * (rRCSetupComplete_IEs__guami_Type__Type
  option * (rRCSetupComplete_IEs__s_NSSAI_List__Type
  option * (dedicatedNAS_Message__Type * (rRCSetupComplete_IEs__ng_5G_S_TMSI_Value__Type
  option * (octet_string option * (rRCSetupComplete_v1610_IEs__Type
  option * unit)))))))

val rRCSetupComplete_IEs__F2 : seq_type -> rRCSetupComplete_IEs__Type

val rRCSetupComplete_IEs__Format : rRCSetupComplete_IEs__Type t_Format

type rRCSetupComplete__criticalExtensions__criticalExtensionsFuture__Type =
| Make__RRCSetupComplete__criticalExtensions__criticalExtensionsFuture__Type

type rRCSetupComplete__criticalExtensions__Type =
| RRCSetupComplete__criticalExtensions__rrcSetupComplete of rRCSetupComplete_IEs__Type
| RRCSetupComplete__criticalExtensions__criticalExtensionsFuture of rRCSetupComplete__criticalExtensions__criticalExtensionsFuture__Type

type rRCSetupComplete__Type = { rRCSetupComplete__rrc_TransactionIdentifier : 
                                rRC_TransactionIdentifier__Type;
                                rRCSetupComplete__criticalExtensions : 
                                rRCSetupComplete__criticalExtensions__Type }

val rRCSetupComplete__list : seq_elem list

val rRCSetupComplete__criticalExtensions__criticalExtensionsFuture__Format :
  rRCSetupComplete__criticalExtensions__criticalExtensionsFuture__Type t_Format

val rRCSetupComplete__criticalExtensions__list__Format :
  (int, __) sigT t_Format

val rRCSetupComplete__criticalExtensions__F1 :
  rRCSetupComplete__criticalExtensions__Type -> choice

val rRCSetupComplete__criticalExtensions__F2 :
  choice -> rRCSetupComplete__criticalExtensions__Type

val rRCSetupComplete__criticalExtensions__Format :
  rRCSetupComplete__criticalExtensions__Type t_Format

type rRCSetupComplete__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val rRCSetupComplete__Format_list : rRCSetupComplete__Format_Type

val rRCSetupComplete__list__Format : seq_type t_Format

val rRCSetupComplete__F1 :
  rRCSetupComplete__Type ->
  rRC_TransactionIdentifier__Type * (rRCSetupComplete__criticalExtensions__Type * unit)

val rRCSetupComplete__F2 : seq_type -> rRCSetupComplete__Type

val rRCSetupComplete__Format : rRCSetupComplete__Type t_Format

type rRCReestablishmentComplete_v1610_IEs__nonCriticalExtension__Type =
| Make__RRCReestablishmentComplete_v1610_IEs__nonCriticalExtension__Type

type rRCReestablishmentComplete_v1610_IEs__Type = { rRCReestablishmentComplete_v1610_IEs__ue_MeasurementsAvailable_r16 : 
                                                    uE_MeasurementsAvailable_r16__Type
                                                    option;
                                                    rRCReestablishmentComplete_v1610_IEs__nonCriticalExtension : 
                                                    rRCReestablishmentComplete_v1610_IEs__nonCriticalExtension__Type
                                                    option }

val rRCReestablishmentComplete_v1610_IEs__list : seq_elem list

val rRCReestablishmentComplete_v1610_IEs__nonCriticalExtension__Format :
  rRCReestablishmentComplete_v1610_IEs__nonCriticalExtension__Type t_Format

type rRCReestablishmentComplete_v1610_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val rRCReestablishmentComplete_v1610_IEs__Format_list :
  rRCReestablishmentComplete_v1610_IEs__Format_Type

val rRCReestablishmentComplete_v1610_IEs__list__Format : seq_type t_Format

val rRCReestablishmentComplete_v1610_IEs__F1 :
  rRCReestablishmentComplete_v1610_IEs__Type ->
  uE_MeasurementsAvailable_r16__Type
  option * (rRCReestablishmentComplete_v1610_IEs__nonCriticalExtension__Type
  option * unit)

val rRCReestablishmentComplete_v1610_IEs__F2 :
  seq_type -> rRCReestablishmentComplete_v1610_IEs__Type

val rRCReestablishmentComplete_v1610_IEs__Format :
  rRCReestablishmentComplete_v1610_IEs__Type t_Format

type rRCReestablishmentComplete_IEs__Type = { rRCReestablishmentComplete_IEs__lateNonCriticalExtension : 
                                              octet_string option;
                                              rRCReestablishmentComplete_IEs__nonCriticalExtension : 
                                              rRCReestablishmentComplete_v1610_IEs__Type
                                              option }

val rRCReestablishmentComplete_IEs__list : seq_elem list

type rRCReestablishmentComplete_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val rRCReestablishmentComplete_IEs__Format_list :
  rRCReestablishmentComplete_IEs__Format_Type

val rRCReestablishmentComplete_IEs__list__Format : seq_type t_Format

val rRCReestablishmentComplete_IEs__F1 :
  rRCReestablishmentComplete_IEs__Type -> octet_string
  option * (rRCReestablishmentComplete_v1610_IEs__Type option * unit)

val rRCReestablishmentComplete_IEs__F2 :
  seq_type -> rRCReestablishmentComplete_IEs__Type

val rRCReestablishmentComplete_IEs__Format :
  rRCReestablishmentComplete_IEs__Type t_Format

type rRCReestablishmentComplete__criticalExtensions__criticalExtensionsFuture__Type =
| Make__RRCReestablishmentComplete__criticalExtensions__criticalExtensionsFuture__Type

type rRCReestablishmentComplete__criticalExtensions__Type =
| RRCReestablishmentComplete__criticalExtensions__rrcReestablishmentComplete of 
   rRCReestablishmentComplete_IEs__Type
| RRCReestablishmentComplete__criticalExtensions__criticalExtensionsFuture of 
   rRCReestablishmentComplete__criticalExtensions__criticalExtensionsFuture__Type

type rRCReestablishmentComplete__Type = { rRCReestablishmentComplete__rrc_TransactionIdentifier : 
                                          rRC_TransactionIdentifier__Type;
                                          rRCReestablishmentComplete__criticalExtensions : 
                                          rRCReestablishmentComplete__criticalExtensions__Type }

val rRCReestablishmentComplete__list : seq_elem list

val rRCReestablishmentComplete__criticalExtensions__criticalExtensionsFuture__Format :
  rRCReestablishmentComplete__criticalExtensions__criticalExtensionsFuture__Type
  t_Format

val rRCReestablishmentComplete__criticalExtensions__list__Format :
  (int, __) sigT t_Format

val rRCReestablishmentComplete__criticalExtensions__F1 :
  rRCReestablishmentComplete__criticalExtensions__Type -> choice

val rRCReestablishmentComplete__criticalExtensions__F2 :
  choice -> rRCReestablishmentComplete__criticalExtensions__Type

val rRCReestablishmentComplete__criticalExtensions__Format :
  rRCReestablishmentComplete__criticalExtensions__Type t_Format

type rRCReestablishmentComplete__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val rRCReestablishmentComplete__Format_list :
  rRCReestablishmentComplete__Format_Type

val rRCReestablishmentComplete__list__Format : seq_type t_Format

val rRCReestablishmentComplete__F1 :
  rRCReestablishmentComplete__Type ->
  rRC_TransactionIdentifier__Type * (rRCReestablishmentComplete__criticalExtensions__Type * unit)

val rRCReestablishmentComplete__F2 :
  seq_type -> rRCReestablishmentComplete__Type

val rRCReestablishmentComplete__Format :
  rRCReestablishmentComplete__Type t_Format

type rSRQ_RangeEUTRA_r16__Type = int

val rSRQ_RangeEUTRA_r16__Format : int t_Format

type measResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__Type = { 
measResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__rsrp_ResultEUTRA_r16 : 
rSRP_RangeEUTRA__Type option;
measResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__rsrq_ResultEUTRA_r16 : 
rSRQ_RangeEUTRA_r16__Type option }

val measResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__list :
  seq_elem list

type measResultsPerCellIdleEUTRA_r16__Type = { measResultsPerCellIdleEUTRA_r16__eutra_PhysCellId_r16 : 
                                               eUTRA_PhysCellId__Type;
                                               measResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16 : 
                                               measResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__Type }

val measResultsPerCellIdleEUTRA_r16__root_list : seq_elem list

val measResultsPerCellIdleEUTRA_r16__ext_list : typ list

type measResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val measResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__Format_list :
  measResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__Format_Type

val measResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__list__Format :
  seq_type t_Format

val measResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__F1 :
  measResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__Type ->
  rSRP_RangeEUTRA__Type option * (rSRQ_RangeEUTRA_r16__Type option * unit)

val measResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__F2 :
  seq_type -> measResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__Type

val measResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__Format :
  measResultsPerCellIdleEUTRA_r16__measIdleResultEUTRA_r16__Type t_Format

type measResultsPerCellIdleEUTRA_r16__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val measResultsPerCellIdleEUTRA_r16__root_Format_list :
  measResultsPerCellIdleEUTRA_r16__root_Format_Type

type measResultsPerCellIdleEUTRA_r16__ext_Format_Type = unit t_Format

val measResultsPerCellIdleEUTRA_r16__ext_Format_list :
  measResultsPerCellIdleEUTRA_r16__ext_Format_Type

type measResultsPerCellIdleEUTRA_r16__list_type = seq_type * seq_ext_type

val measResultsPerCellIdleEUTRA_r16__list_format :
  measResultsPerCellIdleEUTRA_r16__list_type t_Format

val measResultsPerCellIdleEUTRA_r16__F1 :
  measResultsPerCellIdleEUTRA_r16__Type ->
  measResultsPerCellIdleEUTRA_r16__list_type

val measResultsPerCellIdleEUTRA_r16__F2 :
  measResultsPerCellIdleEUTRA_r16__list_type ->
  measResultsPerCellIdleEUTRA_r16__Type

val measResultsPerCellIdleEUTRA_r16__Format :
  measResultsPerCellIdleEUTRA_r16__Type t_Format

type measResultsPerCarrierIdleEUTRA_r16__measResultsPerCellListIdleEUTRA_r16__Type =
  measResultsPerCellIdleEUTRA_r16__Type list

type measResultsPerCarrierIdleEUTRA_r16__Type = { measResultsPerCarrierIdleEUTRA_r16__carrierFreqEUTRA_r16 : 
                                                  aRFCN_ValueEUTRA__Type;
                                                  measResultsPerCarrierIdleEUTRA_r16__measResultsPerCellListIdleEUTRA_r16 : 
                                                  measResultsPerCarrierIdleEUTRA_r16__measResultsPerCellListIdleEUTRA_r16__Type }

val measResultsPerCarrierIdleEUTRA_r16__root_list : seq_elem list

val measResultsPerCarrierIdleEUTRA_r16__ext_list : typ list

val measResultsPerCarrierIdleEUTRA_r16__measResultsPerCellListIdleEUTRA_r16__Format :
  measResultsPerCarrierIdleEUTRA_r16__measResultsPerCellListIdleEUTRA_r16__Type
  t_Format

type measResultsPerCarrierIdleEUTRA_r16__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val measResultsPerCarrierIdleEUTRA_r16__root_Format_list :
  measResultsPerCarrierIdleEUTRA_r16__root_Format_Type

type measResultsPerCarrierIdleEUTRA_r16__ext_Format_Type = unit t_Format

val measResultsPerCarrierIdleEUTRA_r16__ext_Format_list :
  measResultsPerCarrierIdleEUTRA_r16__ext_Format_Type

type measResultsPerCarrierIdleEUTRA_r16__list_type = seq_type * seq_ext_type

val measResultsPerCarrierIdleEUTRA_r16__list_format :
  measResultsPerCarrierIdleEUTRA_r16__list_type t_Format

val measResultsPerCarrierIdleEUTRA_r16__F1 :
  measResultsPerCarrierIdleEUTRA_r16__Type ->
  measResultsPerCarrierIdleEUTRA_r16__list_type

val measResultsPerCarrierIdleEUTRA_r16__F2 :
  measResultsPerCarrierIdleEUTRA_r16__list_type ->
  measResultsPerCarrierIdleEUTRA_r16__Type

val measResultsPerCarrierIdleEUTRA_r16__Format :
  measResultsPerCarrierIdleEUTRA_r16__Type t_Format

type measResultIdleEUTRA_r16__measResultsPerCarrierListIdleEUTRA_r16__Type =
  measResultsPerCarrierIdleEUTRA_r16__Type list

type measResultIdleEUTRA_r16__Type = { measResultIdleEUTRA_r16__measResultsPerCarrierListIdleEUTRA_r16 : 
                                       measResultIdleEUTRA_r16__measResultsPerCarrierListIdleEUTRA_r16__Type }

val measResultIdleEUTRA_r16__root_list : seq_elem list

val measResultIdleEUTRA_r16__ext_list : typ list

val measResultIdleEUTRA_r16__measResultsPerCarrierListIdleEUTRA_r16__Format :
  measResultIdleEUTRA_r16__measResultsPerCarrierListIdleEUTRA_r16__Type
  t_Format

type measResultIdleEUTRA_r16__root_Format_Type =
  seq_elem_to_format * seq_elem_to_format

val measResultIdleEUTRA_r16__root_Format_list :
  measResultIdleEUTRA_r16__root_Format_Type

type measResultIdleEUTRA_r16__ext_Format_Type = unit t_Format

val measResultIdleEUTRA_r16__ext_Format_list :
  measResultIdleEUTRA_r16__ext_Format_Type

type measResultIdleEUTRA_r16__list_type = seq_type * seq_ext_type

val measResultIdleEUTRA_r16__list_format :
  measResultIdleEUTRA_r16__list_type t_Format

val measResultIdleEUTRA_r16__F1 :
  measResultIdleEUTRA_r16__Type -> measResultIdleEUTRA_r16__list_type

val measResultIdleEUTRA_r16__F2 :
  measResultIdleEUTRA_r16__list_type -> measResultIdleEUTRA_r16__Type

val measResultIdleEUTRA_r16__Format : measResultIdleEUTRA_r16__Type t_Format

type resultsPerSSB_IndexIdle_r16__ssb_Results_r16__Type = { resultsPerSSB_IndexIdle_r16__ssb_Results_r16__ssb_RSRP_Result_r16 : 
                                                            rSRP_Range__Type
                                                            option;
                                                            resultsPerSSB_IndexIdle_r16__ssb_Results_r16__ssb_RSRQ_Result_r16 : 
                                                            rSRQ_Range__Type
                                                            option }

val resultsPerSSB_IndexIdle_r16__ssb_Results_r16__list : seq_elem list

type resultsPerSSB_IndexIdle_r16__Type = { resultsPerSSB_IndexIdle_r16__ssb_Index_r16 : 
                                           sSB_Index__Type;
                                           resultsPerSSB_IndexIdle_r16__ssb_Results_r16 : 
                                           resultsPerSSB_IndexIdle_r16__ssb_Results_r16__Type
                                           option }

val resultsPerSSB_IndexIdle_r16__list : seq_elem list

type resultsPerSSB_IndexIdle_r16__ssb_Results_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val resultsPerSSB_IndexIdle_r16__ssb_Results_r16__Format_list :
  resultsPerSSB_IndexIdle_r16__ssb_Results_r16__Format_Type

val resultsPerSSB_IndexIdle_r16__ssb_Results_r16__list__Format :
  seq_type t_Format

val resultsPerSSB_IndexIdle_r16__ssb_Results_r16__F1 :
  resultsPerSSB_IndexIdle_r16__ssb_Results_r16__Type -> rSRP_Range__Type
  option * (rSRQ_Range__Type option * unit)

val resultsPerSSB_IndexIdle_r16__ssb_Results_r16__F2 :
  seq_type -> resultsPerSSB_IndexIdle_r16__ssb_Results_r16__Type

val resultsPerSSB_IndexIdle_r16__ssb_Results_r16__Format :
  resultsPerSSB_IndexIdle_r16__ssb_Results_r16__Type t_Format

type resultsPerSSB_IndexIdle_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val resultsPerSSB_IndexIdle_r16__Format_list :
  resultsPerSSB_IndexIdle_r16__Format_Type

val resultsPerSSB_IndexIdle_r16__list__Format : seq_type t_Format

val resultsPerSSB_IndexIdle_r16__F1 :
  resultsPerSSB_IndexIdle_r16__Type ->
  sSB_Index__Type * (resultsPerSSB_IndexIdle_r16__ssb_Results_r16__Type
  option * unit)

val resultsPerSSB_IndexIdle_r16__F2 :
  seq_type -> resultsPerSSB_IndexIdle_r16__Type

val resultsPerSSB_IndexIdle_r16__Format :
  resultsPerSSB_IndexIdle_r16__Type t_Format

type resultsPerSSB_IndexList_r16__Type = resultsPerSSB_IndexIdle_r16__Type list

val resultsPerSSB_IndexList_r16__Format :
  resultsPerSSB_IndexList_r16__Type t_Format

type measResultsPerCellIdleNR_r16__measIdleResultNR_r16__Type = { measResultsPerCellIdleNR_r16__measIdleResultNR_r16__rsrp_Result_r16 : 
                                                                  rSRP_Range__Type
                                                                  option;
                                                                  measResultsPerCellIdleNR_r16__measIdleResultNR_r16__rsrq_Result_r16 : 
                                                                  rSRQ_Range__Type
                                                                  option;
                                                                  measResultsPerCellIdleNR_r16__measIdleResultNR_r16__resultsSSB_Indexes_r16 : 
                                                                  resultsPerSSB_IndexList_r16__Type
                                                                  option }

val measResultsPerCellIdleNR_r16__measIdleResultNR_r16__list : seq_elem list

type measResultsPerCellIdleNR_r16__Type = { measResultsPerCellIdleNR_r16__physCellId_r16 : 
                                            physCellId__Type;
                                            measResultsPerCellIdleNR_r16__measIdleResultNR_r16 : 
                                            measResultsPerCellIdleNR_r16__measIdleResultNR_r16__Type }

val measResultsPerCellIdleNR_r16__root_list : seq_elem list

val measResultsPerCellIdleNR_r16__ext_list : typ list

type measResultsPerCellIdleNR_r16__measIdleResultNR_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val measResultsPerCellIdleNR_r16__measIdleResultNR_r16__Format_list :
  measResultsPerCellIdleNR_r16__measIdleResultNR_r16__Format_Type

val measResultsPerCellIdleNR_r16__measIdleResultNR_r16__list__Format :
  seq_type t_Format

val measResultsPerCellIdleNR_r16__measIdleResultNR_r16__F1 :
  measResultsPerCellIdleNR_r16__measIdleResultNR_r16__Type -> rSRP_Range__Type
  option * (rSRQ_Range__Type option * (resultsPerSSB_IndexList_r16__Type
  option * unit))

val measResultsPerCellIdleNR_r16__measIdleResultNR_r16__F2 :
  seq_type -> measResultsPerCellIdleNR_r16__measIdleResultNR_r16__Type

val measResultsPerCellIdleNR_r16__measIdleResultNR_r16__Format :
  measResultsPerCellIdleNR_r16__measIdleResultNR_r16__Type t_Format

type measResultsPerCellIdleNR_r16__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val measResultsPerCellIdleNR_r16__root_Format_list :
  measResultsPerCellIdleNR_r16__root_Format_Type

type measResultsPerCellIdleNR_r16__ext_Format_Type = unit t_Format

val measResultsPerCellIdleNR_r16__ext_Format_list :
  measResultsPerCellIdleNR_r16__ext_Format_Type

type measResultsPerCellIdleNR_r16__list_type = seq_type * seq_ext_type

val measResultsPerCellIdleNR_r16__list_format :
  measResultsPerCellIdleNR_r16__list_type t_Format

val measResultsPerCellIdleNR_r16__F1 :
  measResultsPerCellIdleNR_r16__Type -> measResultsPerCellIdleNR_r16__list_type

val measResultsPerCellIdleNR_r16__F2 :
  measResultsPerCellIdleNR_r16__list_type -> measResultsPerCellIdleNR_r16__Type

val measResultsPerCellIdleNR_r16__Format :
  measResultsPerCellIdleNR_r16__Type t_Format

type measResultsPerCarrierIdleNR_r16__measResultsPerCellListIdleNR_r16__Type =
  measResultsPerCellIdleNR_r16__Type list

type measResultsPerCarrierIdleNR_r16__Type = { measResultsPerCarrierIdleNR_r16__carrierFreq_r16 : 
                                               aRFCN_ValueNR__Type;
                                               measResultsPerCarrierIdleNR_r16__measResultsPerCellListIdleNR_r16 : 
                                               measResultsPerCarrierIdleNR_r16__measResultsPerCellListIdleNR_r16__Type }

val measResultsPerCarrierIdleNR_r16__root_list : seq_elem list

val measResultsPerCarrierIdleNR_r16__ext_list : typ list

val measResultsPerCarrierIdleNR_r16__measResultsPerCellListIdleNR_r16__Format :
  measResultsPerCarrierIdleNR_r16__measResultsPerCellListIdleNR_r16__Type
  t_Format

type measResultsPerCarrierIdleNR_r16__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val measResultsPerCarrierIdleNR_r16__root_Format_list :
  measResultsPerCarrierIdleNR_r16__root_Format_Type

type measResultsPerCarrierIdleNR_r16__ext_Format_Type = unit t_Format

val measResultsPerCarrierIdleNR_r16__ext_Format_list :
  measResultsPerCarrierIdleNR_r16__ext_Format_Type

type measResultsPerCarrierIdleNR_r16__list_type = seq_type * seq_ext_type

val measResultsPerCarrierIdleNR_r16__list_format :
  measResultsPerCarrierIdleNR_r16__list_type t_Format

val measResultsPerCarrierIdleNR_r16__F1 :
  measResultsPerCarrierIdleNR_r16__Type ->
  measResultsPerCarrierIdleNR_r16__list_type

val measResultsPerCarrierIdleNR_r16__F2 :
  measResultsPerCarrierIdleNR_r16__list_type ->
  measResultsPerCarrierIdleNR_r16__Type

val measResultsPerCarrierIdleNR_r16__Format :
  measResultsPerCarrierIdleNR_r16__Type t_Format

type measResultIdleNR_r16__measResultServingCell_r16__Type = { measResultIdleNR_r16__measResultServingCell_r16__rsrp_Result_r16 : 
                                                               rSRP_Range__Type
                                                               option;
                                                               measResultIdleNR_r16__measResultServingCell_r16__rsrq_Result_r16 : 
                                                               rSRQ_Range__Type
                                                               option;
                                                               measResultIdleNR_r16__measResultServingCell_r16__resultsSSB_Indexes_r16 : 
                                                               resultsPerSSB_IndexList_r16__Type
                                                               option }

val measResultIdleNR_r16__measResultServingCell_r16__list : seq_elem list

type measResultIdleNR_r16__measResultsPerCarrierListIdleNR_r16__Type =
  measResultsPerCarrierIdleNR_r16__Type list

type measResultIdleNR_r16__Type = { measResultIdleNR_r16__measResultServingCell_r16 : 
                                    measResultIdleNR_r16__measResultServingCell_r16__Type;
                                    measResultIdleNR_r16__measResultsPerCarrierListIdleNR_r16 : 
                                    measResultIdleNR_r16__measResultsPerCarrierListIdleNR_r16__Type
                                    option }

val measResultIdleNR_r16__root_list : seq_elem list

val measResultIdleNR_r16__ext_list : typ list

type measResultIdleNR_r16__measResultServingCell_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val measResultIdleNR_r16__measResultServingCell_r16__Format_list :
  measResultIdleNR_r16__measResultServingCell_r16__Format_Type

val measResultIdleNR_r16__measResultServingCell_r16__list__Format :
  seq_type t_Format

val measResultIdleNR_r16__measResultServingCell_r16__F1 :
  measResultIdleNR_r16__measResultServingCell_r16__Type -> rSRP_Range__Type
  option * (rSRQ_Range__Type option * (resultsPerSSB_IndexList_r16__Type
  option * unit))

val measResultIdleNR_r16__measResultServingCell_r16__F2 :
  seq_type -> measResultIdleNR_r16__measResultServingCell_r16__Type

val measResultIdleNR_r16__measResultServingCell_r16__Format :
  measResultIdleNR_r16__measResultServingCell_r16__Type t_Format

val measResultIdleNR_r16__measResultsPerCarrierListIdleNR_r16__Format :
  measResultIdleNR_r16__measResultsPerCarrierListIdleNR_r16__Type t_Format

type measResultIdleNR_r16__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val measResultIdleNR_r16__root_Format_list :
  measResultIdleNR_r16__root_Format_Type

type measResultIdleNR_r16__ext_Format_Type = unit t_Format

val measResultIdleNR_r16__ext_Format_list :
  measResultIdleNR_r16__ext_Format_Type

type measResultIdleNR_r16__list_type = seq_type * seq_ext_type

val measResultIdleNR_r16__list_format :
  measResultIdleNR_r16__list_type t_Format

val measResultIdleNR_r16__F1 :
  measResultIdleNR_r16__Type -> measResultIdleNR_r16__list_type

val measResultIdleNR_r16__F2 :
  measResultIdleNR_r16__list_type -> measResultIdleNR_r16__Type

val measResultIdleNR_r16__Format : measResultIdleNR_r16__Type t_Format

type rRCResumeComplete_v1720_IEs__nonCriticalExtension__Type =
| Make__RRCResumeComplete_v1720_IEs__nonCriticalExtension__Type

type rRCResumeComplete_v1720_IEs__Type = { rRCResumeComplete_v1720_IEs__uplinkTxDirectCurrentMoreCarrierList_r17 : 
                                           uplinkTxDirectCurrentMoreCarrierList_r17__Type
                                           option;
                                           rRCResumeComplete_v1720_IEs__nonCriticalExtension : 
                                           rRCResumeComplete_v1720_IEs__nonCriticalExtension__Type
                                           option }

val rRCResumeComplete_v1720_IEs__list : seq_elem list

val rRCResumeComplete_v1720_IEs__nonCriticalExtension__Format :
  rRCResumeComplete_v1720_IEs__nonCriticalExtension__Type t_Format

type rRCResumeComplete_v1720_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val rRCResumeComplete_v1720_IEs__Format_list :
  rRCResumeComplete_v1720_IEs__Format_Type

val rRCResumeComplete_v1720_IEs__list__Format : seq_type t_Format

val rRCResumeComplete_v1720_IEs__F1 :
  rRCResumeComplete_v1720_IEs__Type ->
  uplinkTxDirectCurrentMoreCarrierList_r17__Type
  option * (rRCResumeComplete_v1720_IEs__nonCriticalExtension__Type
  option * unit)

val rRCResumeComplete_v1720_IEs__F2 :
  seq_type -> rRCResumeComplete_v1720_IEs__Type

val rRCResumeComplete_v1720_IEs__Format :
  rRCResumeComplete_v1720_IEs__Type t_Format

type rRCResumeComplete_v1700_IEs__Type = { rRCResumeComplete_v1700_IEs__needForGapNCSG_InfoNR_r17 : 
                                           needForGapNCSG_InfoNR_r17__Type
                                           option;
                                           rRCResumeComplete_v1700_IEs__needForGapNCSG_InfoEUTRA_r17 : 
                                           needForGapNCSG_InfoEUTRA_r17__Type
                                           option;
                                           rRCResumeComplete_v1700_IEs__nonCriticalExtension : 
                                           rRCResumeComplete_v1720_IEs__Type
                                           option }

val rRCResumeComplete_v1700_IEs__list : seq_elem list

type rRCResumeComplete_v1700_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val rRCResumeComplete_v1700_IEs__Format_list :
  rRCResumeComplete_v1700_IEs__Format_Type

val rRCResumeComplete_v1700_IEs__list__Format : seq_type t_Format

val rRCResumeComplete_v1700_IEs__F1 :
  rRCResumeComplete_v1700_IEs__Type -> needForGapNCSG_InfoNR_r17__Type
  option * (needForGapNCSG_InfoEUTRA_r17__Type
  option * (rRCResumeComplete_v1720_IEs__Type option * unit))

val rRCResumeComplete_v1700_IEs__F2 :
  seq_type -> rRCResumeComplete_v1700_IEs__Type

val rRCResumeComplete_v1700_IEs__Format :
  rRCResumeComplete_v1700_IEs__Type t_Format

type rRCResumeComplete_v1640_IEs__Type = { rRCResumeComplete_v1640_IEs__uplinkTxDirectCurrentTwoCarrierList_r16 : 
                                           uplinkTxDirectCurrentTwoCarrierList_r16__Type
                                           option;
                                           rRCResumeComplete_v1640_IEs__nonCriticalExtension : 
                                           rRCResumeComplete_v1700_IEs__Type
                                           option }

val rRCResumeComplete_v1640_IEs__list : seq_elem list

type rRCResumeComplete_v1640_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val rRCResumeComplete_v1640_IEs__Format_list :
  rRCResumeComplete_v1640_IEs__Format_Type

val rRCResumeComplete_v1640_IEs__list__Format : seq_type t_Format

val rRCResumeComplete_v1640_IEs__F1 :
  rRCResumeComplete_v1640_IEs__Type ->
  uplinkTxDirectCurrentTwoCarrierList_r16__Type
  option * (rRCResumeComplete_v1700_IEs__Type option * unit)

val rRCResumeComplete_v1640_IEs__F2 :
  seq_type -> rRCResumeComplete_v1640_IEs__Type

val rRCResumeComplete_v1640_IEs__Format :
  rRCResumeComplete_v1640_IEs__Type t_Format

type rRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__Type =
| RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__true

val rRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__nat__Format :
  int t_Format

val rRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__F1 :
  rRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__Type -> int

val rRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__F2 :
  int -> rRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__Type

type rRCResumeComplete_v1610_IEs__scg_Response_r16__Type =
| RRCResumeComplete_v1610_IEs__scg_Response_r16__nr_SCG_Response of octet_string
| RRCResumeComplete_v1610_IEs__scg_Response_r16__eutra_SCG_Response of 
   octet_string

type rRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__Type =
| RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__true

val rRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__nat__Format :
  int t_Format

val rRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__F1 :
  rRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__Type -> int

val rRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__F2 :
  int -> rRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__Type

type rRCResumeComplete_v1610_IEs__mobilityState_r16__Type =
| RRCResumeComplete_v1610_IEs__mobilityState_r16__normal
| RRCResumeComplete_v1610_IEs__mobilityState_r16__medium
| RRCResumeComplete_v1610_IEs__mobilityState_r16__high
| RRCResumeComplete_v1610_IEs__mobilityState_r16__spare

val rRCResumeComplete_v1610_IEs__mobilityState_r16__nat__Format : int t_Format

val rRCResumeComplete_v1610_IEs__mobilityState_r16__F1 :
  rRCResumeComplete_v1610_IEs__mobilityState_r16__Type -> int

val rRCResumeComplete_v1610_IEs__mobilityState_r16__F2 :
  int -> rRCResumeComplete_v1610_IEs__mobilityState_r16__Type

type rRCResumeComplete_v1610_IEs__Type = { rRCResumeComplete_v1610_IEs__idleMeasAvailable_r16 : 
                                           rRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__Type
                                           option;
                                           rRCResumeComplete_v1610_IEs__measResultIdleEUTRA_r16 : 
                                           measResultIdleEUTRA_r16__Type option;
                                           rRCResumeComplete_v1610_IEs__measResultIdleNR_r16 : 
                                           measResultIdleNR_r16__Type option;
                                           rRCResumeComplete_v1610_IEs__scg_Response_r16 : 
                                           rRCResumeComplete_v1610_IEs__scg_Response_r16__Type
                                           option;
                                           rRCResumeComplete_v1610_IEs__ue_MeasurementsAvailable_r16 : 
                                           uE_MeasurementsAvailable_r16__Type
                                           option;
                                           rRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16 : 
                                           rRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__Type
                                           option;
                                           rRCResumeComplete_v1610_IEs__mobilityState_r16 : 
                                           rRCResumeComplete_v1610_IEs__mobilityState_r16__Type
                                           option;
                                           rRCResumeComplete_v1610_IEs__needForGapsInfoNR_r16 : 
                                           needForGapsInfoNR_r16__Type option;
                                           rRCResumeComplete_v1610_IEs__nonCriticalExtension : 
                                           rRCResumeComplete_v1640_IEs__Type
                                           option }

val rRCResumeComplete_v1610_IEs__list : seq_elem list

val rRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__Format :
  rRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__Type t_Format

val rRCResumeComplete_v1610_IEs__scg_Response_r16__list__Format :
  (int, __) sigT t_Format

val rRCResumeComplete_v1610_IEs__scg_Response_r16__F1 :
  rRCResumeComplete_v1610_IEs__scg_Response_r16__Type -> choice

val rRCResumeComplete_v1610_IEs__scg_Response_r16__F2 :
  choice -> rRCResumeComplete_v1610_IEs__scg_Response_r16__Type

val rRCResumeComplete_v1610_IEs__scg_Response_r16__Format :
  rRCResumeComplete_v1610_IEs__scg_Response_r16__Type t_Format

val rRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__Format :
  rRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__Type t_Format

val rRCResumeComplete_v1610_IEs__mobilityState_r16__Format :
  rRCResumeComplete_v1610_IEs__mobilityState_r16__Type t_Format

type rRCResumeComplete_v1610_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))))))))

val rRCResumeComplete_v1610_IEs__Format_list :
  rRCResumeComplete_v1610_IEs__Format_Type

val rRCResumeComplete_v1610_IEs__list__Format : seq_type t_Format

val rRCResumeComplete_v1610_IEs__F1 :
  rRCResumeComplete_v1610_IEs__Type ->
  rRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__Type
  option * (measResultIdleEUTRA_r16__Type option * (measResultIdleNR_r16__Type
  option * (rRCResumeComplete_v1610_IEs__scg_Response_r16__Type
  option * (uE_MeasurementsAvailable_r16__Type
  option * (rRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__Type
  option * (rRCResumeComplete_v1610_IEs__mobilityState_r16__Type
  option * (needForGapsInfoNR_r16__Type
  option * (rRCResumeComplete_v1640_IEs__Type option * unit))))))))

val rRCResumeComplete_v1610_IEs__F2 :
  seq_type -> rRCResumeComplete_v1610_IEs__Type

val rRCResumeComplete_v1610_IEs__Format :
  rRCResumeComplete_v1610_IEs__Type t_Format

type rRCResumeComplete_IEs__Type = { rRCResumeComplete_IEs__dedicatedNAS_Message : 
                                     dedicatedNAS_Message__Type option;
                                     rRCResumeComplete_IEs__selectedPLMN_Identity : 
                                     int option;
                                     rRCResumeComplete_IEs__uplinkTxDirectCurrentList : 
                                     uplinkTxDirectCurrentList__Type option;
                                     rRCResumeComplete_IEs__lateNonCriticalExtension : 
                                     octet_string option;
                                     rRCResumeComplete_IEs__nonCriticalExtension : 
                                     rRCResumeComplete_v1610_IEs__Type option }

val rRCResumeComplete_IEs__list : seq_elem list

val rRCResumeComplete_IEs__selectedPLMN_Identity__Format : int t_Format

type rRCResumeComplete_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))))

val rRCResumeComplete_IEs__Format_list : rRCResumeComplete_IEs__Format_Type

val rRCResumeComplete_IEs__list__Format : seq_type t_Format

val rRCResumeComplete_IEs__F1 :
  rRCResumeComplete_IEs__Type -> dedicatedNAS_Message__Type option * (int
  option * (uplinkTxDirectCurrentList__Type option * (octet_string
  option * (rRCResumeComplete_v1610_IEs__Type option * unit))))

val rRCResumeComplete_IEs__F2 : seq_type -> rRCResumeComplete_IEs__Type

val rRCResumeComplete_IEs__Format : rRCResumeComplete_IEs__Type t_Format

type rRCResumeComplete__criticalExtensions__criticalExtensionsFuture__Type =
| Make__RRCResumeComplete__criticalExtensions__criticalExtensionsFuture__Type

type rRCResumeComplete__criticalExtensions__Type =
| RRCResumeComplete__criticalExtensions__rrcResumeComplete of rRCResumeComplete_IEs__Type
| RRCResumeComplete__criticalExtensions__criticalExtensionsFuture of rRCResumeComplete__criticalExtensions__criticalExtensionsFuture__Type

type rRCResumeComplete__Type = { rRCResumeComplete__rrc_TransactionIdentifier : 
                                 rRC_TransactionIdentifier__Type;
                                 rRCResumeComplete__criticalExtensions : 
                                 rRCResumeComplete__criticalExtensions__Type }

val rRCResumeComplete__list : seq_elem list

val rRCResumeComplete__criticalExtensions__criticalExtensionsFuture__Format :
  rRCResumeComplete__criticalExtensions__criticalExtensionsFuture__Type
  t_Format

val rRCResumeComplete__criticalExtensions__list__Format :
  (int, __) sigT t_Format

val rRCResumeComplete__criticalExtensions__F1 :
  rRCResumeComplete__criticalExtensions__Type -> choice

val rRCResumeComplete__criticalExtensions__F2 :
  choice -> rRCResumeComplete__criticalExtensions__Type

val rRCResumeComplete__criticalExtensions__Format :
  rRCResumeComplete__criticalExtensions__Type t_Format

type rRCResumeComplete__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val rRCResumeComplete__Format_list : rRCResumeComplete__Format_Type

val rRCResumeComplete__list__Format : seq_type t_Format

val rRCResumeComplete__F1 :
  rRCResumeComplete__Type ->
  rRC_TransactionIdentifier__Type * (rRCResumeComplete__criticalExtensions__Type * unit)

val rRCResumeComplete__F2 : seq_type -> rRCResumeComplete__Type

val rRCResumeComplete__Format : rRCResumeComplete__Type t_Format

type securityModeComplete_IEs__nonCriticalExtension__Type =
| Make__SecurityModeComplete_IEs__nonCriticalExtension__Type

type securityModeComplete_IEs__Type = { securityModeComplete_IEs__lateNonCriticalExtension : 
                                        octet_string option;
                                        securityModeComplete_IEs__nonCriticalExtension : 
                                        securityModeComplete_IEs__nonCriticalExtension__Type
                                        option }

val securityModeComplete_IEs__list : seq_elem list

val securityModeComplete_IEs__nonCriticalExtension__Format :
  securityModeComplete_IEs__nonCriticalExtension__Type t_Format

type securityModeComplete_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val securityModeComplete_IEs__Format_list :
  securityModeComplete_IEs__Format_Type

val securityModeComplete_IEs__list__Format : seq_type t_Format

val securityModeComplete_IEs__F1 :
  securityModeComplete_IEs__Type -> octet_string
  option * (securityModeComplete_IEs__nonCriticalExtension__Type option * unit)

val securityModeComplete_IEs__F2 : seq_type -> securityModeComplete_IEs__Type

val securityModeComplete_IEs__Format : securityModeComplete_IEs__Type t_Format

type securityModeComplete__criticalExtensions__criticalExtensionsFuture__Type =
| Make__SecurityModeComplete__criticalExtensions__criticalExtensionsFuture__Type

type securityModeComplete__criticalExtensions__Type =
| SecurityModeComplete__criticalExtensions__securityModeComplete of securityModeComplete_IEs__Type
| SecurityModeComplete__criticalExtensions__criticalExtensionsFuture of 
   securityModeComplete__criticalExtensions__criticalExtensionsFuture__Type

type securityModeComplete__Type = { securityModeComplete__rrc_TransactionIdentifier : 
                                    rRC_TransactionIdentifier__Type;
                                    securityModeComplete__criticalExtensions : 
                                    securityModeComplete__criticalExtensions__Type }

val securityModeComplete__list : seq_elem list

val securityModeComplete__criticalExtensions__criticalExtensionsFuture__Format :
  securityModeComplete__criticalExtensions__criticalExtensionsFuture__Type
  t_Format

val securityModeComplete__criticalExtensions__list__Format :
  (int, __) sigT t_Format

val securityModeComplete__criticalExtensions__F1 :
  securityModeComplete__criticalExtensions__Type -> choice

val securityModeComplete__criticalExtensions__F2 :
  choice -> securityModeComplete__criticalExtensions__Type

val securityModeComplete__criticalExtensions__Format :
  securityModeComplete__criticalExtensions__Type t_Format

type securityModeComplete__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val securityModeComplete__Format_list : securityModeComplete__Format_Type

val securityModeComplete__list__Format : seq_type t_Format

val securityModeComplete__F1 :
  securityModeComplete__Type ->
  rRC_TransactionIdentifier__Type * (securityModeComplete__criticalExtensions__Type * unit)

val securityModeComplete__F2 : seq_type -> securityModeComplete__Type

val securityModeComplete__Format : securityModeComplete__Type t_Format

type securityModeFailure_IEs__nonCriticalExtension__Type =
| Make__SecurityModeFailure_IEs__nonCriticalExtension__Type

type securityModeFailure_IEs__Type = { securityModeFailure_IEs__lateNonCriticalExtension : 
                                       octet_string option;
                                       securityModeFailure_IEs__nonCriticalExtension : 
                                       securityModeFailure_IEs__nonCriticalExtension__Type
                                       option }

val securityModeFailure_IEs__list : seq_elem list

val securityModeFailure_IEs__nonCriticalExtension__Format :
  securityModeFailure_IEs__nonCriticalExtension__Type t_Format

type securityModeFailure_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val securityModeFailure_IEs__Format_list : securityModeFailure_IEs__Format_Type

val securityModeFailure_IEs__list__Format : seq_type t_Format

val securityModeFailure_IEs__F1 :
  securityModeFailure_IEs__Type -> octet_string
  option * (securityModeFailure_IEs__nonCriticalExtension__Type option * unit)

val securityModeFailure_IEs__F2 : seq_type -> securityModeFailure_IEs__Type

val securityModeFailure_IEs__Format : securityModeFailure_IEs__Type t_Format

type securityModeFailure__criticalExtensions__criticalExtensionsFuture__Type =
| Make__SecurityModeFailure__criticalExtensions__criticalExtensionsFuture__Type

type securityModeFailure__criticalExtensions__Type =
| SecurityModeFailure__criticalExtensions__securityModeFailure of securityModeFailure_IEs__Type
| SecurityModeFailure__criticalExtensions__criticalExtensionsFuture of 
   securityModeFailure__criticalExtensions__criticalExtensionsFuture__Type

type securityModeFailure__Type = { securityModeFailure__rrc_TransactionIdentifier : 
                                   rRC_TransactionIdentifier__Type;
                                   securityModeFailure__criticalExtensions : 
                                   securityModeFailure__criticalExtensions__Type }

val securityModeFailure__list : seq_elem list

val securityModeFailure__criticalExtensions__criticalExtensionsFuture__Format :
  securityModeFailure__criticalExtensions__criticalExtensionsFuture__Type
  t_Format

val securityModeFailure__criticalExtensions__list__Format :
  (int, __) sigT t_Format

val securityModeFailure__criticalExtensions__F1 :
  securityModeFailure__criticalExtensions__Type -> choice

val securityModeFailure__criticalExtensions__F2 :
  choice -> securityModeFailure__criticalExtensions__Type

val securityModeFailure__criticalExtensions__Format :
  securityModeFailure__criticalExtensions__Type t_Format

type securityModeFailure__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val securityModeFailure__Format_list : securityModeFailure__Format_Type

val securityModeFailure__list__Format : seq_type t_Format

val securityModeFailure__F1 :
  securityModeFailure__Type ->
  rRC_TransactionIdentifier__Type * (securityModeFailure__criticalExtensions__Type * unit)

val securityModeFailure__F2 : seq_type -> securityModeFailure__Type

val securityModeFailure__Format : securityModeFailure__Type t_Format

type dedicatedInfoF1c_r17__Type = octet_string

val dedicatedInfoF1c_r17__Format : char list t_Format

type uLInformationTransfer_v1700_IEs__nonCriticalExtension__Type =
| Make__ULInformationTransfer_v1700_IEs__nonCriticalExtension__Type

type uLInformationTransfer_v1700_IEs__Type = { uLInformationTransfer_v1700_IEs__dedicatedInfoF1c_r17 : 
                                               dedicatedInfoF1c_r17__Type
                                               option;
                                               uLInformationTransfer_v1700_IEs__nonCriticalExtension : 
                                               uLInformationTransfer_v1700_IEs__nonCriticalExtension__Type
                                               option }

val uLInformationTransfer_v1700_IEs__list : seq_elem list

val uLInformationTransfer_v1700_IEs__nonCriticalExtension__Format :
  uLInformationTransfer_v1700_IEs__nonCriticalExtension__Type t_Format

type uLInformationTransfer_v1700_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val uLInformationTransfer_v1700_IEs__Format_list :
  uLInformationTransfer_v1700_IEs__Format_Type

val uLInformationTransfer_v1700_IEs__list__Format : seq_type t_Format

val uLInformationTransfer_v1700_IEs__F1 :
  uLInformationTransfer_v1700_IEs__Type -> dedicatedInfoF1c_r17__Type
  option * (uLInformationTransfer_v1700_IEs__nonCriticalExtension__Type
  option * unit)

val uLInformationTransfer_v1700_IEs__F2 :
  seq_type -> uLInformationTransfer_v1700_IEs__Type

val uLInformationTransfer_v1700_IEs__Format :
  uLInformationTransfer_v1700_IEs__Type t_Format

type uLInformationTransfer_IEs__Type = { uLInformationTransfer_IEs__dedicatedNAS_Message : 
                                         dedicatedNAS_Message__Type option;
                                         uLInformationTransfer_IEs__lateNonCriticalExtension : 
                                         octet_string option;
                                         uLInformationTransfer_IEs__nonCriticalExtension : 
                                         uLInformationTransfer_v1700_IEs__Type
                                         option }

val uLInformationTransfer_IEs__list : seq_elem list

type uLInformationTransfer_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val uLInformationTransfer_IEs__Format_list :
  uLInformationTransfer_IEs__Format_Type

val uLInformationTransfer_IEs__list__Format : seq_type t_Format

val uLInformationTransfer_IEs__F1 :
  uLInformationTransfer_IEs__Type -> dedicatedNAS_Message__Type
  option * (octet_string option * (uLInformationTransfer_v1700_IEs__Type
  option * unit))

val uLInformationTransfer_IEs__F2 : seq_type -> uLInformationTransfer_IEs__Type

val uLInformationTransfer_IEs__Format :
  uLInformationTransfer_IEs__Type t_Format

type uLInformationTransfer__criticalExtensions__criticalExtensionsFuture__Type =
| Make__ULInformationTransfer__criticalExtensions__criticalExtensionsFuture__Type

type uLInformationTransfer__criticalExtensions__Type =
| ULInformationTransfer__criticalExtensions__ulInformationTransfer of 
   uLInformationTransfer_IEs__Type
| ULInformationTransfer__criticalExtensions__criticalExtensionsFuture of 
   uLInformationTransfer__criticalExtensions__criticalExtensionsFuture__Type

type uLInformationTransfer__Type = { uLInformationTransfer__criticalExtensions : 
                                     uLInformationTransfer__criticalExtensions__Type }

val uLInformationTransfer__list : seq_elem list

val uLInformationTransfer__criticalExtensions__criticalExtensionsFuture__Format :
  uLInformationTransfer__criticalExtensions__criticalExtensionsFuture__Type
  t_Format

val uLInformationTransfer__criticalExtensions__list__Format :
  (int, __) sigT t_Format

val uLInformationTransfer__criticalExtensions__F1 :
  uLInformationTransfer__criticalExtensions__Type -> choice

val uLInformationTransfer__criticalExtensions__F2 :
  choice -> uLInformationTransfer__criticalExtensions__Type

val uLInformationTransfer__criticalExtensions__Format :
  uLInformationTransfer__criticalExtensions__Type t_Format

type uLInformationTransfer__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val uLInformationTransfer__Format_list : uLInformationTransfer__Format_Type

val uLInformationTransfer__list__Format : seq_type t_Format

val uLInformationTransfer__F1 :
  uLInformationTransfer__Type ->
  uLInformationTransfer__criticalExtensions__Type * unit

val uLInformationTransfer__F2 : seq_type -> uLInformationTransfer__Type

val uLInformationTransfer__Format : uLInformationTransfer__Type t_Format

type 'elementTypeParam__Type setupRelease__Type =
| SetupRelease__release of unit
| SetupRelease__setup of 'elementTypeParam__Type

val setupRelease__list__Format : 'a1 t_Format -> (int, __) sigT t_Format

val setupRelease__F1 : 'a1 setupRelease__Type -> choice

val setupRelease__F2 : choice -> 'a1 setupRelease__Type

val setupRelease__Format : 'a1 t_Format -> 'a1 setupRelease__Type t_Format

type eUTRA_RSTD_Info__Type = { eUTRA_RSTD_Info__carrierFreq : aRFCN_ValueEUTRA__Type;
                               eUTRA_RSTD_Info__measPRS_Offset : int }

val eUTRA_RSTD_Info__root_list : seq_elem list

val eUTRA_RSTD_Info__ext_list : typ list

val eUTRA_RSTD_Info__measPRS_Offset__Format : int t_Format

type eUTRA_RSTD_Info__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val eUTRA_RSTD_Info__root_Format_list : eUTRA_RSTD_Info__root_Format_Type

type eUTRA_RSTD_Info__ext_Format_Type = unit t_Format

val eUTRA_RSTD_Info__ext_Format_list : eUTRA_RSTD_Info__ext_Format_Type

type eUTRA_RSTD_Info__list_type = seq_type * seq_ext_type

val eUTRA_RSTD_Info__list_format : eUTRA_RSTD_Info__list_type t_Format

val eUTRA_RSTD_Info__F1 : eUTRA_RSTD_Info__Type -> eUTRA_RSTD_Info__list_type

val eUTRA_RSTD_Info__F2 : eUTRA_RSTD_Info__list_type -> eUTRA_RSTD_Info__Type

val eUTRA_RSTD_Info__Format : eUTRA_RSTD_Info__Type t_Format

type eUTRA_RSTD_InfoList__Type = eUTRA_RSTD_Info__Type list

val eUTRA_RSTD_InfoList__Format : eUTRA_RSTD_InfoList__Type t_Format

type nR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__Type =
| NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms20_r16 of 
   int
| NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms40_r16 of 
   int
| NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms80_r16 of 
   int
| NR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms160_r16 of 
   int

type nR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__ext__Type =
  empty_set

type nR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__Type =
  (nR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__Type,
  nR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__ext__Type)
  sum

type nR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__Type =
| NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__ms1dot5
| NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__ms3
| NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__ms3dot5
| NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__ms4
| NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__ms5dot5
| NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__ms6
| NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__ms10
| NR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__ms20

val nR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__nat__Format :
  int t_Format

val nR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__F1 :
  nR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__Type -> int

val nR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__F2 :
  int -> nR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__Type

type nR_PRS_MeasurementInfo_r16__Type = { nR_PRS_MeasurementInfo_r16__dl_PRS_PointA_r16 : 
                                          aRFCN_ValueNR__Type;
                                          nR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16 : 
                                          nR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__Type;
                                          nR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16 : 
                                          nR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__Type }

val nR_PRS_MeasurementInfo_r16__root_list : seq_elem list

val nR_PRS_MeasurementInfo_r16__ext_list : typ list

val nR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms20_r16__Format :
  int t_Format

val nR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms40_r16__Format :
  int t_Format

val nR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms80_r16__Format :
  int t_Format

val nR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__ms160_r16__Format :
  int t_Format

val nR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__list__Format :
  (int, __) sigT t_Format

val nR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__F1 :
  nR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__Type
  -> choice

val nR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__F2 :
  choice ->
  nR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__Type

val nR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__Format :
  nR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__root__Type
  t_Format

val nR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__ext__Format :
  nR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__ext__Type
  t_Format

val nR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__Format :
  nR_PRS_MeasurementInfo_r16__nr_MeasPRS_RepetitionAndOffset_r16__Type t_Format

val nR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__Format :
  nR_PRS_MeasurementInfo_r16__nr_MeasPRS_length_r16__Type t_Format

type nR_PRS_MeasurementInfo_r16__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val nR_PRS_MeasurementInfo_r16__root_Format_list :
  nR_PRS_MeasurementInfo_r16__root_Format_Type

type nR_PRS_MeasurementInfo_r16__ext_Format_Type = unit t_Format

val nR_PRS_MeasurementInfo_r16__ext_Format_list :
  nR_PRS_MeasurementInfo_r16__ext_Format_Type

type nR_PRS_MeasurementInfo_r16__list_type = seq_type * seq_ext_type

val nR_PRS_MeasurementInfo_r16__list_format :
  nR_PRS_MeasurementInfo_r16__list_type t_Format

val nR_PRS_MeasurementInfo_r16__F1 :
  nR_PRS_MeasurementInfo_r16__Type -> nR_PRS_MeasurementInfo_r16__list_type

val nR_PRS_MeasurementInfo_r16__F2 :
  nR_PRS_MeasurementInfo_r16__list_type -> nR_PRS_MeasurementInfo_r16__Type

val nR_PRS_MeasurementInfo_r16__Format :
  nR_PRS_MeasurementInfo_r16__Type t_Format

type nR_PRS_MeasurementInfoList_r16__Type =
  nR_PRS_MeasurementInfo_r16__Type list

val nR_PRS_MeasurementInfoList_r16__Format :
  nR_PRS_MeasurementInfoList_r16__Type t_Format

type locationMeasurementInfo__root__Type =
| LocationMeasurementInfo__root__eutra_RSTD of eUTRA_RSTD_InfoList__Type

type locationMeasurementInfo__ext__Type =
| LocationMeasurementInfo__ext__eutra_FineTimingDetection of unit
| LocationMeasurementInfo__ext__nr_PRS_Measurement_r16 of nR_PRS_MeasurementInfoList_r16__Type

type locationMeasurementInfo__Type =
  (locationMeasurementInfo__root__Type, locationMeasurementInfo__ext__Type) sum

val locationMeasurementInfo__root__F1 :
  locationMeasurementInfo__root__Type -> eUTRA_RSTD_InfoList__Type

val locationMeasurementInfo__root__F2 :
  eUTRA_RSTD_InfoList__Type -> locationMeasurementInfo__root__Type

val locationMeasurementInfo__root__Format :
  locationMeasurementInfo__root__Type t_Format

val locationMeasurementInfo__ext__list__Format : (int, __) sigT t_Format

val locationMeasurementInfo__ext__F1 :
  locationMeasurementInfo__ext__Type -> choice

val locationMeasurementInfo__ext__F2 :
  choice -> locationMeasurementInfo__ext__Type

val locationMeasurementInfo__ext__Format :
  locationMeasurementInfo__ext__Type t_Format

val locationMeasurementInfo__Format : locationMeasurementInfo__Type t_Format

type locationMeasurementIndication_IEs__measurementIndication__Type =
  locationMeasurementInfo__Type setupRelease__Type

val locationMeasurementIndication_IEs__measurementIndication__Format :
  locationMeasurementIndication_IEs__measurementIndication__Type t_Format

type locationMeasurementIndication_IEs__nonCriticalExtension__Type =
| Make__LocationMeasurementIndication_IEs__nonCriticalExtension__Type

type locationMeasurementIndication_IEs__Type = { locationMeasurementIndication_IEs__measurementIndication : 
                                                 locationMeasurementIndication_IEs__measurementIndication__Type;
                                                 locationMeasurementIndication_IEs__lateNonCriticalExtension : 
                                                 octet_string option;
                                                 locationMeasurementIndication_IEs__nonCriticalExtension : 
                                                 locationMeasurementIndication_IEs__nonCriticalExtension__Type
                                                 option }

val locationMeasurementIndication_IEs__list : seq_elem list

val locationMeasurementIndication_IEs__nonCriticalExtension__Format :
  locationMeasurementIndication_IEs__nonCriticalExtension__Type t_Format

type locationMeasurementIndication_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val locationMeasurementIndication_IEs__Format_list :
  locationMeasurementIndication_IEs__Format_Type

val locationMeasurementIndication_IEs__list__Format : seq_type t_Format

val locationMeasurementIndication_IEs__F1 :
  locationMeasurementIndication_IEs__Type ->
  locationMeasurementIndication_IEs__measurementIndication__Type * (octet_string
  option * (locationMeasurementIndication_IEs__nonCriticalExtension__Type
  option * unit))

val locationMeasurementIndication_IEs__F2 :
  seq_type -> locationMeasurementIndication_IEs__Type

val locationMeasurementIndication_IEs__Format :
  locationMeasurementIndication_IEs__Type t_Format

type locationMeasurementIndication__criticalExtensions__criticalExtensionsFuture__Type =
| Make__LocationMeasurementIndication__criticalExtensions__criticalExtensionsFuture__Type

type locationMeasurementIndication__criticalExtensions__Type =
| LocationMeasurementIndication__criticalExtensions__locationMeasurementIndication of 
   locationMeasurementIndication_IEs__Type
| LocationMeasurementIndication__criticalExtensions__criticalExtensionsFuture of 
   locationMeasurementIndication__criticalExtensions__criticalExtensionsFuture__Type

type locationMeasurementIndication__Type = { locationMeasurementIndication__criticalExtensions : 
                                             locationMeasurementIndication__criticalExtensions__Type }

val locationMeasurementIndication__list : seq_elem list

val locationMeasurementIndication__criticalExtensions__criticalExtensionsFuture__Format :
  locationMeasurementIndication__criticalExtensions__criticalExtensionsFuture__Type
  t_Format

val locationMeasurementIndication__criticalExtensions__list__Format :
  (int, __) sigT t_Format

val locationMeasurementIndication__criticalExtensions__F1 :
  locationMeasurementIndication__criticalExtensions__Type -> choice

val locationMeasurementIndication__criticalExtensions__F2 :
  choice -> locationMeasurementIndication__criticalExtensions__Type

val locationMeasurementIndication__criticalExtensions__Format :
  locationMeasurementIndication__criticalExtensions__Type t_Format

type locationMeasurementIndication__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val locationMeasurementIndication__Format_list :
  locationMeasurementIndication__Format_Type

val locationMeasurementIndication__list__Format : seq_type t_Format

val locationMeasurementIndication__F1 :
  locationMeasurementIndication__Type ->
  locationMeasurementIndication__criticalExtensions__Type * unit

val locationMeasurementIndication__F2 :
  seq_type -> locationMeasurementIndication__Type

val locationMeasurementIndication__Format :
  locationMeasurementIndication__Type t_Format

type rAT_Type__root__Type =
| RAT_Type__root__nr
| RAT_Type__root__eutra_nr
| RAT_Type__root__eutra
| RAT_Type__root__utra_fdd_v1610

val rAT_Type__root__nat__Format : int t_Format

val rAT_Type__root__F1 : rAT_Type__root__Type -> int

val rAT_Type__root__F2 : int -> rAT_Type__root__Type

type rAT_Type__ext__Type = empty_set

type rAT_Type__Type = (rAT_Type__root__Type, rAT_Type__ext__Type) sum

val rAT_Type__root__Format : rAT_Type__root__Type t_Format

val rAT_Type__ext__Format : rAT_Type__ext__Type t_Format

val rAT_Type__Format : rAT_Type__Type t_Format

type uE_CapabilityRAT_Container__Type = { uE_CapabilityRAT_Container__rat_Type : 
                                          rAT_Type__Type;
                                          uE_CapabilityRAT_Container__ue_CapabilityRAT_Container : 
                                          octet_string }

val uE_CapabilityRAT_Container__list : seq_elem list

type uE_CapabilityRAT_Container__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val uE_CapabilityRAT_Container__Format_list :
  uE_CapabilityRAT_Container__Format_Type

val uE_CapabilityRAT_Container__list__Format : seq_type t_Format

val uE_CapabilityRAT_Container__F1 :
  uE_CapabilityRAT_Container__Type -> rAT_Type__Type * (octet_string * unit)

val uE_CapabilityRAT_Container__F2 :
  seq_type -> uE_CapabilityRAT_Container__Type

val uE_CapabilityRAT_Container__Format :
  uE_CapabilityRAT_Container__Type t_Format

type uE_CapabilityRAT_ContainerList__Type =
  uE_CapabilityRAT_Container__Type list

val uE_CapabilityRAT_ContainerList__Format :
  uE_CapabilityRAT_ContainerList__Type t_Format

type uECapabilityInformation_IEs__nonCriticalExtension__Type =
| Make__UECapabilityInformation_IEs__nonCriticalExtension__Type

type uECapabilityInformation_IEs__Type = { uECapabilityInformation_IEs__ue_CapabilityRAT_ContainerList : 
                                           uE_CapabilityRAT_ContainerList__Type
                                           option;
                                           uECapabilityInformation_IEs__lateNonCriticalExtension : 
                                           octet_string option;
                                           uECapabilityInformation_IEs__nonCriticalExtension : 
                                           uECapabilityInformation_IEs__nonCriticalExtension__Type
                                           option }

val uECapabilityInformation_IEs__list : seq_elem list

val uECapabilityInformation_IEs__nonCriticalExtension__Format :
  uECapabilityInformation_IEs__nonCriticalExtension__Type t_Format

type uECapabilityInformation_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val uECapabilityInformation_IEs__Format_list :
  uECapabilityInformation_IEs__Format_Type

val uECapabilityInformation_IEs__list__Format : seq_type t_Format

val uECapabilityInformation_IEs__F1 :
  uECapabilityInformation_IEs__Type -> uE_CapabilityRAT_ContainerList__Type
  option * (octet_string
  option * (uECapabilityInformation_IEs__nonCriticalExtension__Type
  option * unit))

val uECapabilityInformation_IEs__F2 :
  seq_type -> uECapabilityInformation_IEs__Type

val uECapabilityInformation_IEs__Format :
  uECapabilityInformation_IEs__Type t_Format

type uECapabilityInformation__criticalExtensions__criticalExtensionsFuture__Type =
| Make__UECapabilityInformation__criticalExtensions__criticalExtensionsFuture__Type

type uECapabilityInformation__criticalExtensions__Type =
| UECapabilityInformation__criticalExtensions__ueCapabilityInformation of 
   uECapabilityInformation_IEs__Type
| UECapabilityInformation__criticalExtensions__criticalExtensionsFuture of 
   uECapabilityInformation__criticalExtensions__criticalExtensionsFuture__Type

type uECapabilityInformation__Type = { uECapabilityInformation__rrc_TransactionIdentifier : 
                                       rRC_TransactionIdentifier__Type;
                                       uECapabilityInformation__criticalExtensions : 
                                       uECapabilityInformation__criticalExtensions__Type }

val uECapabilityInformation__list : seq_elem list

val uECapabilityInformation__criticalExtensions__criticalExtensionsFuture__Format :
  uECapabilityInformation__criticalExtensions__criticalExtensionsFuture__Type
  t_Format

val uECapabilityInformation__criticalExtensions__list__Format :
  (int, __) sigT t_Format

val uECapabilityInformation__criticalExtensions__F1 :
  uECapabilityInformation__criticalExtensions__Type -> choice

val uECapabilityInformation__criticalExtensions__F2 :
  choice -> uECapabilityInformation__criticalExtensions__Type

val uECapabilityInformation__criticalExtensions__Format :
  uECapabilityInformation__criticalExtensions__Type t_Format

type uECapabilityInformation__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val uECapabilityInformation__Format_list : uECapabilityInformation__Format_Type

val uECapabilityInformation__list__Format : seq_type t_Format

val uECapabilityInformation__F1 :
  uECapabilityInformation__Type ->
  rRC_TransactionIdentifier__Type * (uECapabilityInformation__criticalExtensions__Type * unit)

val uECapabilityInformation__F2 : seq_type -> uECapabilityInformation__Type

val uECapabilityInformation__Format : uECapabilityInformation__Type t_Format

type dRB_CountInfo__Type = { dRB_CountInfo__drb_Identity : dRB_Identity__Type;
                             dRB_CountInfo__count_Uplink : int;
                             dRB_CountInfo__count_Downlink : int }

val dRB_CountInfo__list : seq_elem list

val dRB_CountInfo__count_Uplink__Format : int t_Format

val dRB_CountInfo__count_Downlink__Format : int t_Format

type dRB_CountInfo__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val dRB_CountInfo__Format_list : dRB_CountInfo__Format_Type

val dRB_CountInfo__list__Format : seq_type t_Format

val dRB_CountInfo__F1 :
  dRB_CountInfo__Type -> dRB_Identity__Type * (int * (int * unit))

val dRB_CountInfo__F2 : seq_type -> dRB_CountInfo__Type

val dRB_CountInfo__Format : dRB_CountInfo__Type t_Format

type dRB_CountInfoList__Type = dRB_CountInfo__Type list

val dRB_CountInfoList__Format : dRB_CountInfoList__Type t_Format

type counterCheckResponse_IEs__nonCriticalExtension__Type =
| Make__CounterCheckResponse_IEs__nonCriticalExtension__Type

type counterCheckResponse_IEs__Type = { counterCheckResponse_IEs__drb_CountInfoList : 
                                        dRB_CountInfoList__Type;
                                        counterCheckResponse_IEs__lateNonCriticalExtension : 
                                        octet_string option;
                                        counterCheckResponse_IEs__nonCriticalExtension : 
                                        counterCheckResponse_IEs__nonCriticalExtension__Type
                                        option }

val counterCheckResponse_IEs__list : seq_elem list

val counterCheckResponse_IEs__nonCriticalExtension__Format :
  counterCheckResponse_IEs__nonCriticalExtension__Type t_Format

type counterCheckResponse_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val counterCheckResponse_IEs__Format_list :
  counterCheckResponse_IEs__Format_Type

val counterCheckResponse_IEs__list__Format : seq_type t_Format

val counterCheckResponse_IEs__F1 :
  counterCheckResponse_IEs__Type -> dRB_CountInfoList__Type * (octet_string
  option * (counterCheckResponse_IEs__nonCriticalExtension__Type
  option * unit))

val counterCheckResponse_IEs__F2 : seq_type -> counterCheckResponse_IEs__Type

val counterCheckResponse_IEs__Format : counterCheckResponse_IEs__Type t_Format

type counterCheckResponse__criticalExtensions__criticalExtensionsFuture__Type =
| Make__CounterCheckResponse__criticalExtensions__criticalExtensionsFuture__Type

type counterCheckResponse__criticalExtensions__Type =
| CounterCheckResponse__criticalExtensions__counterCheckResponse of counterCheckResponse_IEs__Type
| CounterCheckResponse__criticalExtensions__criticalExtensionsFuture of 
   counterCheckResponse__criticalExtensions__criticalExtensionsFuture__Type

type counterCheckResponse__Type = { counterCheckResponse__rrc_TransactionIdentifier : 
                                    rRC_TransactionIdentifier__Type;
                                    counterCheckResponse__criticalExtensions : 
                                    counterCheckResponse__criticalExtensions__Type }

val counterCheckResponse__list : seq_elem list

val counterCheckResponse__criticalExtensions__criticalExtensionsFuture__Format :
  counterCheckResponse__criticalExtensions__criticalExtensionsFuture__Type
  t_Format

val counterCheckResponse__criticalExtensions__list__Format :
  (int, __) sigT t_Format

val counterCheckResponse__criticalExtensions__F1 :
  counterCheckResponse__criticalExtensions__Type -> choice

val counterCheckResponse__criticalExtensions__F2 :
  choice -> counterCheckResponse__criticalExtensions__Type

val counterCheckResponse__criticalExtensions__Format :
  counterCheckResponse__criticalExtensions__Type t_Format

type counterCheckResponse__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val counterCheckResponse__Format_list : counterCheckResponse__Format_Type

val counterCheckResponse__list__Format : seq_type t_Format

val counterCheckResponse__F1 :
  counterCheckResponse__Type ->
  rRC_TransactionIdentifier__Type * (counterCheckResponse__criticalExtensions__Type * unit)

val counterCheckResponse__F2 : seq_type -> counterCheckResponse__Type

val counterCheckResponse__Format : counterCheckResponse__Type t_Format

type delayBudgetReport__root__type1__Type =
| DelayBudgetReport__root__type1__msMinus1280
| DelayBudgetReport__root__type1__msMinus640
| DelayBudgetReport__root__type1__msMinus320
| DelayBudgetReport__root__type1__msMinus160
| DelayBudgetReport__root__type1__msMinus80
| DelayBudgetReport__root__type1__msMinus60
| DelayBudgetReport__root__type1__msMinus40
| DelayBudgetReport__root__type1__msMinus20
| DelayBudgetReport__root__type1__ms0
| DelayBudgetReport__root__type1__ms20
| DelayBudgetReport__root__type1__ms40
| DelayBudgetReport__root__type1__ms60
| DelayBudgetReport__root__type1__ms80
| DelayBudgetReport__root__type1__ms160
| DelayBudgetReport__root__type1__ms320
| DelayBudgetReport__root__type1__ms640
| DelayBudgetReport__root__type1__ms1280

val delayBudgetReport__root__type1__nat__Format : int t_Format

val delayBudgetReport__root__type1__F1 :
  delayBudgetReport__root__type1__Type -> int

val delayBudgetReport__root__type1__F2 :
  int -> delayBudgetReport__root__type1__Type

type delayBudgetReport__root__Type =
| DelayBudgetReport__root__type1 of delayBudgetReport__root__type1__Type

type delayBudgetReport__ext__Type = empty_set

type delayBudgetReport__Type =
  (delayBudgetReport__root__Type, delayBudgetReport__ext__Type) sum

val delayBudgetReport__root__type1__Format :
  delayBudgetReport__root__type1__Type t_Format

val delayBudgetReport__root__F1 :
  delayBudgetReport__root__Type -> delayBudgetReport__root__type1__Type

val delayBudgetReport__root__F2 :
  delayBudgetReport__root__type1__Type -> delayBudgetReport__root__Type

val delayBudgetReport__root__Format : delayBudgetReport__root__Type t_Format

val delayBudgetReport__ext__Format : delayBudgetReport__ext__Type t_Format

val delayBudgetReport__Format : delayBudgetReport__Type t_Format

type reducedMaxCCs_r16__Type = { reducedMaxCCs_r16__reducedCCsDL_r16 : 
                                 int; reducedMaxCCs_r16__reducedCCsUL_r16 : 
                                 int }

val reducedMaxCCs_r16__list : seq_elem list

val reducedMaxCCs_r16__reducedCCsDL_r16__Format : int t_Format

val reducedMaxCCs_r16__reducedCCsUL_r16__Format : int t_Format

type reducedMaxCCs_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val reducedMaxCCs_r16__Format_list : reducedMaxCCs_r16__Format_Type

val reducedMaxCCs_r16__list__Format : seq_type t_Format

val reducedMaxCCs_r16__F1 : reducedMaxCCs_r16__Type -> int * (int * unit)

val reducedMaxCCs_r16__F2 : seq_type -> reducedMaxCCs_r16__Type

val reducedMaxCCs_r16__Format : reducedMaxCCs_r16__Type t_Format

type reducedAggregatedBandwidth__Type =
| ReducedAggregatedBandwidth__mhz0
| ReducedAggregatedBandwidth__mhz10
| ReducedAggregatedBandwidth__mhz20
| ReducedAggregatedBandwidth__mhz30
| ReducedAggregatedBandwidth__mhz40
| ReducedAggregatedBandwidth__mhz50
| ReducedAggregatedBandwidth__mhz60
| ReducedAggregatedBandwidth__mhz80
| ReducedAggregatedBandwidth__mhz100
| ReducedAggregatedBandwidth__mhz200
| ReducedAggregatedBandwidth__mhz300
| ReducedAggregatedBandwidth__mhz400

val reducedAggregatedBandwidth__nat__Format : int t_Format

val reducedAggregatedBandwidth__F1 : reducedAggregatedBandwidth__Type -> int

val reducedAggregatedBandwidth__F2 : int -> reducedAggregatedBandwidth__Type

val reducedAggregatedBandwidth__Format :
  reducedAggregatedBandwidth__Type t_Format

type reducedMaxBW_FRx_r16__Type = { reducedMaxBW_FRx_r16__reducedBW_DL_r16 : 
                                    reducedAggregatedBandwidth__Type;
                                    reducedMaxBW_FRx_r16__reducedBW_UL_r16 : 
                                    reducedAggregatedBandwidth__Type }

val reducedMaxBW_FRx_r16__list : seq_elem list

type reducedMaxBW_FRx_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val reducedMaxBW_FRx_r16__Format_list : reducedMaxBW_FRx_r16__Format_Type

val reducedMaxBW_FRx_r16__list__Format : seq_type t_Format

val reducedMaxBW_FRx_r16__F1 :
  reducedMaxBW_FRx_r16__Type ->
  reducedAggregatedBandwidth__Type * (reducedAggregatedBandwidth__Type * unit)

val reducedMaxBW_FRx_r16__F2 : seq_type -> reducedMaxBW_FRx_r16__Type

val reducedMaxBW_FRx_r16__Format : reducedMaxBW_FRx_r16__Type t_Format

type mIMO_LayersDL__Type =
| MIMO_LayersDL__twoLayers
| MIMO_LayersDL__fourLayers
| MIMO_LayersDL__eightLayers

val mIMO_LayersDL__nat__Format : int t_Format

val mIMO_LayersDL__F1 : mIMO_LayersDL__Type -> int

val mIMO_LayersDL__F2 : int -> mIMO_LayersDL__Type

val mIMO_LayersDL__Format : mIMO_LayersDL__Type t_Format

type mIMO_LayersUL__Type =
| MIMO_LayersUL__oneLayer
| MIMO_LayersUL__twoLayers
| MIMO_LayersUL__fourLayers

val mIMO_LayersUL__nat__Format : int t_Format

val mIMO_LayersUL__F1 : mIMO_LayersUL__Type -> int

val mIMO_LayersUL__F2 : int -> mIMO_LayersUL__Type

val mIMO_LayersUL__Format : mIMO_LayersUL__Type t_Format

type overheatingAssistance__reducedMaxMIMO_LayersFR1__Type = { overheatingAssistance__reducedMaxMIMO_LayersFR1__reducedMIMO_LayersFR1_DL : 
                                                               mIMO_LayersDL__Type;
                                                               overheatingAssistance__reducedMaxMIMO_LayersFR1__reducedMIMO_LayersFR1_UL : 
                                                               mIMO_LayersUL__Type }

val overheatingAssistance__reducedMaxMIMO_LayersFR1__list : seq_elem list

type overheatingAssistance__reducedMaxMIMO_LayersFR2__Type = { overheatingAssistance__reducedMaxMIMO_LayersFR2__reducedMIMO_LayersFR2_DL : 
                                                               mIMO_LayersDL__Type;
                                                               overheatingAssistance__reducedMaxMIMO_LayersFR2__reducedMIMO_LayersFR2_UL : 
                                                               mIMO_LayersUL__Type }

val overheatingAssistance__reducedMaxMIMO_LayersFR2__list : seq_elem list

type overheatingAssistance__Type = { overheatingAssistance__reducedMaxCCs : 
                                     reducedMaxCCs_r16__Type option;
                                     overheatingAssistance__reducedMaxBW_FR1 : 
                                     reducedMaxBW_FRx_r16__Type option;
                                     overheatingAssistance__reducedMaxBW_FR2 : 
                                     reducedMaxBW_FRx_r16__Type option;
                                     overheatingAssistance__reducedMaxMIMO_LayersFR1 : 
                                     overheatingAssistance__reducedMaxMIMO_LayersFR1__Type
                                     option;
                                     overheatingAssistance__reducedMaxMIMO_LayersFR2 : 
                                     overheatingAssistance__reducedMaxMIMO_LayersFR2__Type
                                     option }

val overheatingAssistance__list : seq_elem list

type overheatingAssistance__reducedMaxMIMO_LayersFR1__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val overheatingAssistance__reducedMaxMIMO_LayersFR1__Format_list :
  overheatingAssistance__reducedMaxMIMO_LayersFR1__Format_Type

val overheatingAssistance__reducedMaxMIMO_LayersFR1__list__Format :
  seq_type t_Format

val overheatingAssistance__reducedMaxMIMO_LayersFR1__F1 :
  overheatingAssistance__reducedMaxMIMO_LayersFR1__Type ->
  mIMO_LayersDL__Type * (mIMO_LayersUL__Type * unit)

val overheatingAssistance__reducedMaxMIMO_LayersFR1__F2 :
  seq_type -> overheatingAssistance__reducedMaxMIMO_LayersFR1__Type

val overheatingAssistance__reducedMaxMIMO_LayersFR1__Format :
  overheatingAssistance__reducedMaxMIMO_LayersFR1__Type t_Format

type overheatingAssistance__reducedMaxMIMO_LayersFR2__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val overheatingAssistance__reducedMaxMIMO_LayersFR2__Format_list :
  overheatingAssistance__reducedMaxMIMO_LayersFR2__Format_Type

val overheatingAssistance__reducedMaxMIMO_LayersFR2__list__Format :
  seq_type t_Format

val overheatingAssistance__reducedMaxMIMO_LayersFR2__F1 :
  overheatingAssistance__reducedMaxMIMO_LayersFR2__Type ->
  mIMO_LayersDL__Type * (mIMO_LayersUL__Type * unit)

val overheatingAssistance__reducedMaxMIMO_LayersFR2__F2 :
  seq_type -> overheatingAssistance__reducedMaxMIMO_LayersFR2__Type

val overheatingAssistance__reducedMaxMIMO_LayersFR2__Format :
  overheatingAssistance__reducedMaxMIMO_LayersFR2__Type t_Format

type overheatingAssistance__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))))

val overheatingAssistance__Format_list : overheatingAssistance__Format_Type

val overheatingAssistance__list__Format : seq_type t_Format

val overheatingAssistance__F1 :
  overheatingAssistance__Type -> reducedMaxCCs_r16__Type
  option * (reducedMaxBW_FRx_r16__Type option * (reducedMaxBW_FRx_r16__Type
  option * (overheatingAssistance__reducedMaxMIMO_LayersFR1__Type
  option * (overheatingAssistance__reducedMaxMIMO_LayersFR2__Type
  option * unit))))

val overheatingAssistance__F2 : seq_type -> overheatingAssistance__Type

val overheatingAssistance__Format : overheatingAssistance__Type t_Format

type affectedCarrierFreq_r16__interferenceDirection_r16__Type =
| AffectedCarrierFreq_r16__interferenceDirection_r16__nr
| AffectedCarrierFreq_r16__interferenceDirection_r16__other
| AffectedCarrierFreq_r16__interferenceDirection_r16__both
| AffectedCarrierFreq_r16__interferenceDirection_r16__spare

val affectedCarrierFreq_r16__interferenceDirection_r16__nat__Format :
  int t_Format

val affectedCarrierFreq_r16__interferenceDirection_r16__F1 :
  affectedCarrierFreq_r16__interferenceDirection_r16__Type -> int

val affectedCarrierFreq_r16__interferenceDirection_r16__F2 :
  int -> affectedCarrierFreq_r16__interferenceDirection_r16__Type

type affectedCarrierFreq_r16__Type = { affectedCarrierFreq_r16__carrierFreq_r16 : 
                                       aRFCN_ValueNR__Type;
                                       affectedCarrierFreq_r16__interferenceDirection_r16 : 
                                       affectedCarrierFreq_r16__interferenceDirection_r16__Type }

val affectedCarrierFreq_r16__list : seq_elem list

val affectedCarrierFreq_r16__interferenceDirection_r16__Format :
  affectedCarrierFreq_r16__interferenceDirection_r16__Type t_Format

type affectedCarrierFreq_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val affectedCarrierFreq_r16__Format_list : affectedCarrierFreq_r16__Format_Type

val affectedCarrierFreq_r16__list__Format : seq_type t_Format

val affectedCarrierFreq_r16__F1 :
  affectedCarrierFreq_r16__Type ->
  aRFCN_ValueNR__Type * (affectedCarrierFreq_r16__interferenceDirection_r16__Type * unit)

val affectedCarrierFreq_r16__F2 : seq_type -> affectedCarrierFreq_r16__Type

val affectedCarrierFreq_r16__Format : affectedCarrierFreq_r16__Type t_Format

type affectedCarrierFreqList_r16__Type = affectedCarrierFreq_r16__Type list

val affectedCarrierFreqList_r16__Format :
  affectedCarrierFreqList_r16__Type t_Format

type victimSystemType_r16__gps_r16__Type =
| VictimSystemType_r16__gps_r16__true

val victimSystemType_r16__gps_r16__nat__Format : int t_Format

val victimSystemType_r16__gps_r16__F1 :
  victimSystemType_r16__gps_r16__Type -> int

val victimSystemType_r16__gps_r16__F2 :
  int -> victimSystemType_r16__gps_r16__Type

type victimSystemType_r16__glonass_r16__Type =
| VictimSystemType_r16__glonass_r16__true

val victimSystemType_r16__glonass_r16__nat__Format : int t_Format

val victimSystemType_r16__glonass_r16__F1 :
  victimSystemType_r16__glonass_r16__Type -> int

val victimSystemType_r16__glonass_r16__F2 :
  int -> victimSystemType_r16__glonass_r16__Type

type victimSystemType_r16__bds_r16__Type =
| VictimSystemType_r16__bds_r16__true

val victimSystemType_r16__bds_r16__nat__Format : int t_Format

val victimSystemType_r16__bds_r16__F1 :
  victimSystemType_r16__bds_r16__Type -> int

val victimSystemType_r16__bds_r16__F2 :
  int -> victimSystemType_r16__bds_r16__Type

type victimSystemType_r16__galileo_r16__Type =
| VictimSystemType_r16__galileo_r16__true

val victimSystemType_r16__galileo_r16__nat__Format : int t_Format

val victimSystemType_r16__galileo_r16__F1 :
  victimSystemType_r16__galileo_r16__Type -> int

val victimSystemType_r16__galileo_r16__F2 :
  int -> victimSystemType_r16__galileo_r16__Type

type victimSystemType_r16__navIC_r16__Type =
| VictimSystemType_r16__navIC_r16__true

val victimSystemType_r16__navIC_r16__nat__Format : int t_Format

val victimSystemType_r16__navIC_r16__F1 :
  victimSystemType_r16__navIC_r16__Type -> int

val victimSystemType_r16__navIC_r16__F2 :
  int -> victimSystemType_r16__navIC_r16__Type

type victimSystemType_r16__wlan_r16__Type =
| VictimSystemType_r16__wlan_r16__true

val victimSystemType_r16__wlan_r16__nat__Format : int t_Format

val victimSystemType_r16__wlan_r16__F1 :
  victimSystemType_r16__wlan_r16__Type -> int

val victimSystemType_r16__wlan_r16__F2 :
  int -> victimSystemType_r16__wlan_r16__Type

type victimSystemType_r16__bluetooth_r16__Type =
| VictimSystemType_r16__bluetooth_r16__true

val victimSystemType_r16__bluetooth_r16__nat__Format : int t_Format

val victimSystemType_r16__bluetooth_r16__F1 :
  victimSystemType_r16__bluetooth_r16__Type -> int

val victimSystemType_r16__bluetooth_r16__F2 :
  int -> victimSystemType_r16__bluetooth_r16__Type

type victimSystemType_r16__Type = { victimSystemType_r16__gps_r16 : victimSystemType_r16__gps_r16__Type
                                                                    option;
                                    victimSystemType_r16__glonass_r16 : 
                                    victimSystemType_r16__glonass_r16__Type
                                    option;
                                    victimSystemType_r16__bds_r16 : victimSystemType_r16__bds_r16__Type
                                                                    option;
                                    victimSystemType_r16__galileo_r16 : 
                                    victimSystemType_r16__galileo_r16__Type
                                    option;
                                    victimSystemType_r16__navIC_r16 : 
                                    victimSystemType_r16__navIC_r16__Type
                                    option;
                                    victimSystemType_r16__wlan_r16 : victimSystemType_r16__wlan_r16__Type
                                                                     option;
                                    victimSystemType_r16__bluetooth_r16 : 
                                    victimSystemType_r16__bluetooth_r16__Type
                                    option }

val victimSystemType_r16__root_list : seq_elem list

val victimSystemType_r16__ext_list : typ list

val victimSystemType_r16__gps_r16__Format :
  victimSystemType_r16__gps_r16__Type t_Format

val victimSystemType_r16__glonass_r16__Format :
  victimSystemType_r16__glonass_r16__Type t_Format

val victimSystemType_r16__bds_r16__Format :
  victimSystemType_r16__bds_r16__Type t_Format

val victimSystemType_r16__galileo_r16__Format :
  victimSystemType_r16__galileo_r16__Type t_Format

val victimSystemType_r16__navIC_r16__Format :
  victimSystemType_r16__navIC_r16__Type t_Format

val victimSystemType_r16__wlan_r16__Format :
  victimSystemType_r16__wlan_r16__Type t_Format

val victimSystemType_r16__bluetooth_r16__Format :
  victimSystemType_r16__bluetooth_r16__Type t_Format

type victimSystemType_r16__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))))))

val victimSystemType_r16__root_Format_list :
  victimSystemType_r16__root_Format_Type

type victimSystemType_r16__ext_Format_Type = unit t_Format

val victimSystemType_r16__ext_Format_list :
  victimSystemType_r16__ext_Format_Type

type victimSystemType_r16__list_type = seq_type * seq_ext_type

val victimSystemType_r16__list_format :
  victimSystemType_r16__list_type t_Format

val victimSystemType_r16__F1 :
  victimSystemType_r16__Type -> victimSystemType_r16__list_type

val victimSystemType_r16__F2 :
  victimSystemType_r16__list_type -> victimSystemType_r16__Type

val victimSystemType_r16__Format : victimSystemType_r16__Type t_Format

type affectedCarrierFreqComb_r16__affectedCarrierFreqComb_r16__Type =
  aRFCN_ValueNR__Type list

type affectedCarrierFreqComb_r16__Type = { affectedCarrierFreqComb_r16__affectedCarrierFreqComb_r16 : 
                                           affectedCarrierFreqComb_r16__affectedCarrierFreqComb_r16__Type
                                           option;
                                           affectedCarrierFreqComb_r16__victimSystemType_r16 : 
                                           victimSystemType_r16__Type }

val affectedCarrierFreqComb_r16__list : seq_elem list

val affectedCarrierFreqComb_r16__affectedCarrierFreqComb_r16__Format :
  affectedCarrierFreqComb_r16__affectedCarrierFreqComb_r16__Type t_Format

type affectedCarrierFreqComb_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val affectedCarrierFreqComb_r16__Format_list :
  affectedCarrierFreqComb_r16__Format_Type

val affectedCarrierFreqComb_r16__list__Format : seq_type t_Format

val affectedCarrierFreqComb_r16__F1 :
  affectedCarrierFreqComb_r16__Type ->
  affectedCarrierFreqComb_r16__affectedCarrierFreqComb_r16__Type
  option * (victimSystemType_r16__Type * unit)

val affectedCarrierFreqComb_r16__F2 :
  seq_type -> affectedCarrierFreqComb_r16__Type

val affectedCarrierFreqComb_r16__Format :
  affectedCarrierFreqComb_r16__Type t_Format

type affectedCarrierFreqCombList_r16__Type =
  affectedCarrierFreqComb_r16__Type list

val affectedCarrierFreqCombList_r16__Format :
  affectedCarrierFreqCombList_r16__Type t_Format

type iDC_Assistance_r16__Type = { iDC_Assistance_r16__affectedCarrierFreqList_r16 : 
                                  affectedCarrierFreqList_r16__Type option;
                                  iDC_Assistance_r16__affectedCarrierFreqCombList_r16 : 
                                  affectedCarrierFreqCombList_r16__Type option }

val iDC_Assistance_r16__root_list : seq_elem list

val iDC_Assistance_r16__ext_list : typ list

type iDC_Assistance_r16__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val iDC_Assistance_r16__root_Format_list : iDC_Assistance_r16__root_Format_Type

type iDC_Assistance_r16__ext_Format_Type = unit t_Format

val iDC_Assistance_r16__ext_Format_list : iDC_Assistance_r16__ext_Format_Type

type iDC_Assistance_r16__list_type = seq_type * seq_ext_type

val iDC_Assistance_r16__list_format : iDC_Assistance_r16__list_type t_Format

val iDC_Assistance_r16__F1 :
  iDC_Assistance_r16__Type -> iDC_Assistance_r16__list_type

val iDC_Assistance_r16__F2 :
  iDC_Assistance_r16__list_type -> iDC_Assistance_r16__Type

val iDC_Assistance_r16__Format : iDC_Assistance_r16__Type t_Format

type dRX_Preference_r16__preferredDRX_InactivityTimer_r16__Type =
| DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms0
| DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms1
| DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms2
| DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms3
| DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms4
| DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms5
| DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms6
| DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms8
| DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms10
| DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms20
| DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms30
| DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms40
| DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms50
| DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms60
| DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms80
| DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms100
| DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms200
| DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms300
| DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms500
| DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms750
| DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms1280
| DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms1920
| DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms2560
| DRX_Preference_r16__preferredDRX_InactivityTimer_r16__spare9
| DRX_Preference_r16__preferredDRX_InactivityTimer_r16__spare8
| DRX_Preference_r16__preferredDRX_InactivityTimer_r16__spare7
| DRX_Preference_r16__preferredDRX_InactivityTimer_r16__spare6
| DRX_Preference_r16__preferredDRX_InactivityTimer_r16__spare5
| DRX_Preference_r16__preferredDRX_InactivityTimer_r16__spare4
| DRX_Preference_r16__preferredDRX_InactivityTimer_r16__spare3
| DRX_Preference_r16__preferredDRX_InactivityTimer_r16__spare2
| DRX_Preference_r16__preferredDRX_InactivityTimer_r16__spare1

val dRX_Preference_r16__preferredDRX_InactivityTimer_r16__nat__Format :
  int t_Format

val dRX_Preference_r16__preferredDRX_InactivityTimer_r16__F1 :
  dRX_Preference_r16__preferredDRX_InactivityTimer_r16__Type -> int

val dRX_Preference_r16__preferredDRX_InactivityTimer_r16__F2 :
  int -> dRX_Preference_r16__preferredDRX_InactivityTimer_r16__Type

type dRX_Preference_r16__preferredDRX_LongCycle_r16__Type =
| DRX_Preference_r16__preferredDRX_LongCycle_r16__ms10
| DRX_Preference_r16__preferredDRX_LongCycle_r16__ms20
| DRX_Preference_r16__preferredDRX_LongCycle_r16__ms32
| DRX_Preference_r16__preferredDRX_LongCycle_r16__ms40
| DRX_Preference_r16__preferredDRX_LongCycle_r16__ms60
| DRX_Preference_r16__preferredDRX_LongCycle_r16__ms64
| DRX_Preference_r16__preferredDRX_LongCycle_r16__ms70
| DRX_Preference_r16__preferredDRX_LongCycle_r16__ms80
| DRX_Preference_r16__preferredDRX_LongCycle_r16__ms128
| DRX_Preference_r16__preferredDRX_LongCycle_r16__ms160
| DRX_Preference_r16__preferredDRX_LongCycle_r16__ms256
| DRX_Preference_r16__preferredDRX_LongCycle_r16__ms320
| DRX_Preference_r16__preferredDRX_LongCycle_r16__ms512
| DRX_Preference_r16__preferredDRX_LongCycle_r16__ms640
| DRX_Preference_r16__preferredDRX_LongCycle_r16__ms1024
| DRX_Preference_r16__preferredDRX_LongCycle_r16__ms1280
| DRX_Preference_r16__preferredDRX_LongCycle_r16__ms2048
| DRX_Preference_r16__preferredDRX_LongCycle_r16__ms2560
| DRX_Preference_r16__preferredDRX_LongCycle_r16__ms5120
| DRX_Preference_r16__preferredDRX_LongCycle_r16__ms10240
| DRX_Preference_r16__preferredDRX_LongCycle_r16__spare12
| DRX_Preference_r16__preferredDRX_LongCycle_r16__spare11
| DRX_Preference_r16__preferredDRX_LongCycle_r16__spare10
| DRX_Preference_r16__preferredDRX_LongCycle_r16__spare9
| DRX_Preference_r16__preferredDRX_LongCycle_r16__spare8
| DRX_Preference_r16__preferredDRX_LongCycle_r16__spare7
| DRX_Preference_r16__preferredDRX_LongCycle_r16__spare6
| DRX_Preference_r16__preferredDRX_LongCycle_r16__spare5
| DRX_Preference_r16__preferredDRX_LongCycle_r16__spare4
| DRX_Preference_r16__preferredDRX_LongCycle_r16__spare3
| DRX_Preference_r16__preferredDRX_LongCycle_r16__spare2
| DRX_Preference_r16__preferredDRX_LongCycle_r16__spare1

val dRX_Preference_r16__preferredDRX_LongCycle_r16__nat__Format : int t_Format

val dRX_Preference_r16__preferredDRX_LongCycle_r16__F1 :
  dRX_Preference_r16__preferredDRX_LongCycle_r16__Type -> int

val dRX_Preference_r16__preferredDRX_LongCycle_r16__F2 :
  int -> dRX_Preference_r16__preferredDRX_LongCycle_r16__Type

type dRX_Preference_r16__preferredDRX_ShortCycle_r16__Type =
| DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms2
| DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms3
| DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms4
| DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms5
| DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms6
| DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms7
| DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms8
| DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms10
| DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms14
| DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms16
| DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms20
| DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms30
| DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms32
| DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms35
| DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms40
| DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms64
| DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms80
| DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms128
| DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms160
| DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms256
| DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms320
| DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms512
| DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms640
| DRX_Preference_r16__preferredDRX_ShortCycle_r16__spare9
| DRX_Preference_r16__preferredDRX_ShortCycle_r16__spare8
| DRX_Preference_r16__preferredDRX_ShortCycle_r16__spare7
| DRX_Preference_r16__preferredDRX_ShortCycle_r16__spare6
| DRX_Preference_r16__preferredDRX_ShortCycle_r16__spare5
| DRX_Preference_r16__preferredDRX_ShortCycle_r16__spare4
| DRX_Preference_r16__preferredDRX_ShortCycle_r16__spare3
| DRX_Preference_r16__preferredDRX_ShortCycle_r16__spare2
| DRX_Preference_r16__preferredDRX_ShortCycle_r16__spare1

val dRX_Preference_r16__preferredDRX_ShortCycle_r16__nat__Format : int t_Format

val dRX_Preference_r16__preferredDRX_ShortCycle_r16__F1 :
  dRX_Preference_r16__preferredDRX_ShortCycle_r16__Type -> int

val dRX_Preference_r16__preferredDRX_ShortCycle_r16__F2 :
  int -> dRX_Preference_r16__preferredDRX_ShortCycle_r16__Type

type dRX_Preference_r16__Type = { dRX_Preference_r16__preferredDRX_InactivityTimer_r16 : 
                                  dRX_Preference_r16__preferredDRX_InactivityTimer_r16__Type
                                  option;
                                  dRX_Preference_r16__preferredDRX_LongCycle_r16 : 
                                  dRX_Preference_r16__preferredDRX_LongCycle_r16__Type
                                  option;
                                  dRX_Preference_r16__preferredDRX_ShortCycle_r16 : 
                                  dRX_Preference_r16__preferredDRX_ShortCycle_r16__Type
                                  option;
                                  dRX_Preference_r16__preferredDRX_ShortCycleTimer_r16 : 
                                  int option }

val dRX_Preference_r16__list : seq_elem list

val dRX_Preference_r16__preferredDRX_InactivityTimer_r16__Format :
  dRX_Preference_r16__preferredDRX_InactivityTimer_r16__Type t_Format

val dRX_Preference_r16__preferredDRX_LongCycle_r16__Format :
  dRX_Preference_r16__preferredDRX_LongCycle_r16__Type t_Format

val dRX_Preference_r16__preferredDRX_ShortCycle_r16__Format :
  dRX_Preference_r16__preferredDRX_ShortCycle_r16__Type t_Format

val dRX_Preference_r16__preferredDRX_ShortCycleTimer_r16__Format : int t_Format

type dRX_Preference_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

val dRX_Preference_r16__Format_list : dRX_Preference_r16__Format_Type

val dRX_Preference_r16__list__Format : seq_type t_Format

val dRX_Preference_r16__F1 :
  dRX_Preference_r16__Type ->
  dRX_Preference_r16__preferredDRX_InactivityTimer_r16__Type
  option * (dRX_Preference_r16__preferredDRX_LongCycle_r16__Type
  option * (dRX_Preference_r16__preferredDRX_ShortCycle_r16__Type
  option * (int option * unit)))

val dRX_Preference_r16__F2 : seq_type -> dRX_Preference_r16__Type

val dRX_Preference_r16__Format : dRX_Preference_r16__Type t_Format

type maxBW_Preference_r16__Type = { maxBW_Preference_r16__reducedMaxBW_FR1_r16 : 
                                    reducedMaxBW_FRx_r16__Type option;
                                    maxBW_Preference_r16__reducedMaxBW_FR2_r16 : 
                                    reducedMaxBW_FRx_r16__Type option }

val maxBW_Preference_r16__list : seq_elem list

type maxBW_Preference_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val maxBW_Preference_r16__Format_list : maxBW_Preference_r16__Format_Type

val maxBW_Preference_r16__list__Format : seq_type t_Format

val maxBW_Preference_r16__F1 :
  maxBW_Preference_r16__Type -> reducedMaxBW_FRx_r16__Type
  option * (reducedMaxBW_FRx_r16__Type option * unit)

val maxBW_Preference_r16__F2 : seq_type -> maxBW_Preference_r16__Type

val maxBW_Preference_r16__Format : maxBW_Preference_r16__Type t_Format

type maxCC_Preference_r16__Type = { maxCC_Preference_r16__reducedMaxCCs_r16 : 
                                    reducedMaxCCs_r16__Type option }

val maxCC_Preference_r16__list : seq_elem list

type maxCC_Preference_r16__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val maxCC_Preference_r16__Format_list : maxCC_Preference_r16__Format_Type

val maxCC_Preference_r16__list__Format : seq_type t_Format

val maxCC_Preference_r16__F1 :
  maxCC_Preference_r16__Type -> reducedMaxCCs_r16__Type option * unit

val maxCC_Preference_r16__F2 : seq_type -> maxCC_Preference_r16__Type

val maxCC_Preference_r16__Format : maxCC_Preference_r16__Type t_Format

type maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR1_r16__Type = { 
maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR1_r16__reducedMIMO_LayersFR1_DL_r16 : 
int;
maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR1_r16__reducedMIMO_LayersFR1_UL_r16 : 
int }

val maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR1_r16__list :
  seq_elem list

type maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR2_r16__Type = { 
maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR2_r16__reducedMIMO_LayersFR2_DL_r16 : 
int;
maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR2_r16__reducedMIMO_LayersFR2_UL_r16 : 
int }

val maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR2_r16__list :
  seq_elem list

type maxMIMO_LayerPreference_r16__Type = { maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR1_r16 : 
                                           maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR1_r16__Type
                                           option;
                                           maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR2_r16 : 
                                           maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR2_r16__Type
                                           option }

val maxMIMO_LayerPreference_r16__list : seq_elem list

val maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR1_r16__reducedMIMO_LayersFR1_DL_r16__Format :
  int t_Format

val maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR1_r16__reducedMIMO_LayersFR1_UL_r16__Format :
  int t_Format

type maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR1_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR1_r16__Format_list :
  maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR1_r16__Format_Type

val maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR1_r16__list__Format :
  seq_type t_Format

val maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR1_r16__F1 :
  maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR1_r16__Type ->
  int * (int * unit)

val maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR1_r16__F2 :
  seq_type -> maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR1_r16__Type

val maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR1_r16__Format :
  maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR1_r16__Type t_Format

val maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR2_r16__reducedMIMO_LayersFR2_DL_r16__Format :
  int t_Format

val maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR2_r16__reducedMIMO_LayersFR2_UL_r16__Format :
  int t_Format

type maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR2_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR2_r16__Format_list :
  maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR2_r16__Format_Type

val maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR2_r16__list__Format :
  seq_type t_Format

val maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR2_r16__F1 :
  maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR2_r16__Type ->
  int * (int * unit)

val maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR2_r16__F2 :
  seq_type -> maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR2_r16__Type

val maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR2_r16__Format :
  maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR2_r16__Type t_Format

type maxMIMO_LayerPreference_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val maxMIMO_LayerPreference_r16__Format_list :
  maxMIMO_LayerPreference_r16__Format_Type

val maxMIMO_LayerPreference_r16__list__Format : seq_type t_Format

val maxMIMO_LayerPreference_r16__F1 :
  maxMIMO_LayerPreference_r16__Type ->
  maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR1_r16__Type
  option * (maxMIMO_LayerPreference_r16__reducedMaxMIMO_LayersFR2_r16__Type
  option * unit)

val maxMIMO_LayerPreference_r16__F2 :
  seq_type -> maxMIMO_LayerPreference_r16__Type

val maxMIMO_LayerPreference_r16__Format :
  maxMIMO_LayerPreference_r16__Type t_Format

type minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_15kHz_r16__Type =
| MinSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_15kHz_r16__sl1
| MinSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_15kHz_r16__sl2
| MinSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_15kHz_r16__sl4
| MinSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_15kHz_r16__sl6

val minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_15kHz_r16__nat__Format :
  int t_Format

val minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_15kHz_r16__F1 :
  minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_15kHz_r16__Type
  -> int

val minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_15kHz_r16__F2 :
  int ->
  minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_15kHz_r16__Type

type minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_30kHz_r16__Type =
| MinSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_30kHz_r16__sl1
| MinSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_30kHz_r16__sl2
| MinSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_30kHz_r16__sl4
| MinSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_30kHz_r16__sl6

val minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_30kHz_r16__nat__Format :
  int t_Format

val minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_30kHz_r16__F1 :
  minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_30kHz_r16__Type
  -> int

val minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_30kHz_r16__F2 :
  int ->
  minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_30kHz_r16__Type

type minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_60kHz_r16__Type =
| MinSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_60kHz_r16__sl2
| MinSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_60kHz_r16__sl4
| MinSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_60kHz_r16__sl8
| MinSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_60kHz_r16__sl12

val minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_60kHz_r16__nat__Format :
  int t_Format

val minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_60kHz_r16__F1 :
  minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_60kHz_r16__Type
  -> int

val minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_60kHz_r16__F2 :
  int ->
  minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_60kHz_r16__Type

type minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_120kHz_r16__Type =
| MinSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_120kHz_r16__sl2
| MinSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_120kHz_r16__sl4
| MinSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_120kHz_r16__sl8
| MinSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_120kHz_r16__sl12

val minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_120kHz_r16__nat__Format :
  int t_Format

val minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_120kHz_r16__F1 :
  minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_120kHz_r16__Type
  -> int

val minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_120kHz_r16__F2 :
  int ->
  minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_120kHz_r16__Type

type minSchedulingOffsetPreference_r16__preferredK0_r16__Type = { minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_15kHz_r16 : 
                                                                  minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_15kHz_r16__Type
                                                                  option;
                                                                  minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_30kHz_r16 : 
                                                                  minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_30kHz_r16__Type
                                                                  option;
                                                                  minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_60kHz_r16 : 
                                                                  minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_60kHz_r16__Type
                                                                  option;
                                                                  minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_120kHz_r16 : 
                                                                  minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_120kHz_r16__Type
                                                                  option }

val minSchedulingOffsetPreference_r16__preferredK0_r16__list : seq_elem list

type minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_15kHz_r16__Type =
| MinSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_15kHz_r16__sl1
| MinSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_15kHz_r16__sl2
| MinSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_15kHz_r16__sl4
| MinSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_15kHz_r16__sl6

val minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_15kHz_r16__nat__Format :
  int t_Format

val minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_15kHz_r16__F1 :
  minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_15kHz_r16__Type
  -> int

val minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_15kHz_r16__F2 :
  int ->
  minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_15kHz_r16__Type

type minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_30kHz_r16__Type =
| MinSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_30kHz_r16__sl1
| MinSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_30kHz_r16__sl2
| MinSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_30kHz_r16__sl4
| MinSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_30kHz_r16__sl6

val minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_30kHz_r16__nat__Format :
  int t_Format

val minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_30kHz_r16__F1 :
  minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_30kHz_r16__Type
  -> int

val minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_30kHz_r16__F2 :
  int ->
  minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_30kHz_r16__Type

type minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_60kHz_r16__Type =
| MinSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_60kHz_r16__sl2
| MinSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_60kHz_r16__sl4
| MinSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_60kHz_r16__sl8
| MinSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_60kHz_r16__sl12

val minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_60kHz_r16__nat__Format :
  int t_Format

val minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_60kHz_r16__F1 :
  minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_60kHz_r16__Type
  -> int

val minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_60kHz_r16__F2 :
  int ->
  minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_60kHz_r16__Type

type minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_120kHz_r16__Type =
| MinSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_120kHz_r16__sl2
| MinSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_120kHz_r16__sl4
| MinSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_120kHz_r16__sl8
| MinSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_120kHz_r16__sl12

val minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_120kHz_r16__nat__Format :
  int t_Format

val minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_120kHz_r16__F1 :
  minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_120kHz_r16__Type
  -> int

val minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_120kHz_r16__F2 :
  int ->
  minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_120kHz_r16__Type

type minSchedulingOffsetPreference_r16__preferredK2_r16__Type = { minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_15kHz_r16 : 
                                                                  minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_15kHz_r16__Type
                                                                  option;
                                                                  minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_30kHz_r16 : 
                                                                  minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_30kHz_r16__Type
                                                                  option;
                                                                  minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_60kHz_r16 : 
                                                                  minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_60kHz_r16__Type
                                                                  option;
                                                                  minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_120kHz_r16 : 
                                                                  minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_120kHz_r16__Type
                                                                  option }

val minSchedulingOffsetPreference_r16__preferredK2_r16__list : seq_elem list

type minSchedulingOffsetPreference_r16__Type = { minSchedulingOffsetPreference_r16__preferredK0_r16 : 
                                                 minSchedulingOffsetPreference_r16__preferredK0_r16__Type
                                                 option;
                                                 minSchedulingOffsetPreference_r16__preferredK2_r16 : 
                                                 minSchedulingOffsetPreference_r16__preferredK2_r16__Type
                                                 option }

val minSchedulingOffsetPreference_r16__list : seq_elem list

val minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_15kHz_r16__Format :
  minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_15kHz_r16__Type
  t_Format

val minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_30kHz_r16__Format :
  minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_30kHz_r16__Type
  t_Format

val minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_60kHz_r16__Format :
  minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_60kHz_r16__Type
  t_Format

val minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_120kHz_r16__Format :
  minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_120kHz_r16__Type
  t_Format

type minSchedulingOffsetPreference_r16__preferredK0_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

val minSchedulingOffsetPreference_r16__preferredK0_r16__Format_list :
  minSchedulingOffsetPreference_r16__preferredK0_r16__Format_Type

val minSchedulingOffsetPreference_r16__preferredK0_r16__list__Format :
  seq_type t_Format

val minSchedulingOffsetPreference_r16__preferredK0_r16__F1 :
  minSchedulingOffsetPreference_r16__preferredK0_r16__Type ->
  minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_15kHz_r16__Type
  option * (minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_30kHz_r16__Type
  option * (minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_60kHz_r16__Type
  option * (minSchedulingOffsetPreference_r16__preferredK0_r16__preferredK0_SCS_120kHz_r16__Type
  option * unit)))

val minSchedulingOffsetPreference_r16__preferredK0_r16__F2 :
  seq_type -> minSchedulingOffsetPreference_r16__preferredK0_r16__Type

val minSchedulingOffsetPreference_r16__preferredK0_r16__Format :
  minSchedulingOffsetPreference_r16__preferredK0_r16__Type t_Format

val minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_15kHz_r16__Format :
  minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_15kHz_r16__Type
  t_Format

val minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_30kHz_r16__Format :
  minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_30kHz_r16__Type
  t_Format

val minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_60kHz_r16__Format :
  minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_60kHz_r16__Type
  t_Format

val minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_120kHz_r16__Format :
  minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_120kHz_r16__Type
  t_Format

type minSchedulingOffsetPreference_r16__preferredK2_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

val minSchedulingOffsetPreference_r16__preferredK2_r16__Format_list :
  minSchedulingOffsetPreference_r16__preferredK2_r16__Format_Type

val minSchedulingOffsetPreference_r16__preferredK2_r16__list__Format :
  seq_type t_Format

val minSchedulingOffsetPreference_r16__preferredK2_r16__F1 :
  minSchedulingOffsetPreference_r16__preferredK2_r16__Type ->
  minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_15kHz_r16__Type
  option * (minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_30kHz_r16__Type
  option * (minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_60kHz_r16__Type
  option * (minSchedulingOffsetPreference_r16__preferredK2_r16__preferredK2_SCS_120kHz_r16__Type
  option * unit)))

val minSchedulingOffsetPreference_r16__preferredK2_r16__F2 :
  seq_type -> minSchedulingOffsetPreference_r16__preferredK2_r16__Type

val minSchedulingOffsetPreference_r16__preferredK2_r16__Format :
  minSchedulingOffsetPreference_r16__preferredK2_r16__Type t_Format

type minSchedulingOffsetPreference_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val minSchedulingOffsetPreference_r16__Format_list :
  minSchedulingOffsetPreference_r16__Format_Type

val minSchedulingOffsetPreference_r16__list__Format : seq_type t_Format

val minSchedulingOffsetPreference_r16__F1 :
  minSchedulingOffsetPreference_r16__Type ->
  minSchedulingOffsetPreference_r16__preferredK0_r16__Type
  option * (minSchedulingOffsetPreference_r16__preferredK2_r16__Type
  option * unit)

val minSchedulingOffsetPreference_r16__F2 :
  seq_type -> minSchedulingOffsetPreference_r16__Type

val minSchedulingOffsetPreference_r16__Format :
  minSchedulingOffsetPreference_r16__Type t_Format

type releasePreference_r16__preferredRRC_State_r16__Type =
| ReleasePreference_r16__preferredRRC_State_r16__idle
| ReleasePreference_r16__preferredRRC_State_r16__inactive
| ReleasePreference_r16__preferredRRC_State_r16__connected
| ReleasePreference_r16__preferredRRC_State_r16__outOfConnected

val releasePreference_r16__preferredRRC_State_r16__nat__Format : int t_Format

val releasePreference_r16__preferredRRC_State_r16__F1 :
  releasePreference_r16__preferredRRC_State_r16__Type -> int

val releasePreference_r16__preferredRRC_State_r16__F2 :
  int -> releasePreference_r16__preferredRRC_State_r16__Type

type releasePreference_r16__Type = { releasePreference_r16__preferredRRC_State_r16 : 
                                     releasePreference_r16__preferredRRC_State_r16__Type }

val releasePreference_r16__list : seq_elem list

val releasePreference_r16__preferredRRC_State_r16__Format :
  releasePreference_r16__preferredRRC_State_r16__Type t_Format

type releasePreference_r16__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val releasePreference_r16__Format_list : releasePreference_r16__Format_Type

val releasePreference_r16__list__Format : seq_type t_Format

val releasePreference_r16__F1 :
  releasePreference_r16__Type ->
  releasePreference_r16__preferredRRC_State_r16__Type * unit

val releasePreference_r16__F2 : seq_type -> releasePreference_r16__Type

val releasePreference_r16__Format : releasePreference_r16__Type t_Format

type sL_QoS_FlowIdentity_r16__Type = int

val sL_QoS_FlowIdentity_r16__Format : int t_Format

type sL_TrafficPatternInfo_r16__trafficPeriodicity_r16__Type =
| SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms20
| SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms50
| SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms100
| SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms200
| SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms300
| SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms400
| SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms500
| SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms600
| SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms700
| SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms800
| SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms900
| SL_TrafficPatternInfo_r16__trafficPeriodicity_r16__ms1000

val sL_TrafficPatternInfo_r16__trafficPeriodicity_r16__nat__Format :
  int t_Format

val sL_TrafficPatternInfo_r16__trafficPeriodicity_r16__F1 :
  sL_TrafficPatternInfo_r16__trafficPeriodicity_r16__Type -> int

val sL_TrafficPatternInfo_r16__trafficPeriodicity_r16__F2 :
  int -> sL_TrafficPatternInfo_r16__trafficPeriodicity_r16__Type

type sL_TrafficPatternInfo_r16__messageSize_r16__Type = bit_string_fixed

type sL_TrafficPatternInfo_r16__Type = { sL_TrafficPatternInfo_r16__trafficPeriodicity_r16 : 
                                         sL_TrafficPatternInfo_r16__trafficPeriodicity_r16__Type;
                                         sL_TrafficPatternInfo_r16__timingOffset_r16 : 
                                         int;
                                         sL_TrafficPatternInfo_r16__messageSize_r16 : 
                                         sL_TrafficPatternInfo_r16__messageSize_r16__Type;
                                         sL_TrafficPatternInfo_r16__sl_QoS_FlowIdentity_r16 : 
                                         sL_QoS_FlowIdentity_r16__Type }

val sL_TrafficPatternInfo_r16__list : seq_elem list

val sL_TrafficPatternInfo_r16__trafficPeriodicity_r16__Format :
  sL_TrafficPatternInfo_r16__trafficPeriodicity_r16__Type t_Format

val sL_TrafficPatternInfo_r16__timingOffset_r16__Format : int t_Format

val sL_TrafficPatternInfo_r16__messageSize_r16__Format :
  sL_TrafficPatternInfo_r16__messageSize_r16__Type t_Format

type sL_TrafficPatternInfo_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

val sL_TrafficPatternInfo_r16__Format_list :
  sL_TrafficPatternInfo_r16__Format_Type

val sL_TrafficPatternInfo_r16__list__Format : seq_type t_Format

val sL_TrafficPatternInfo_r16__F1 :
  sL_TrafficPatternInfo_r16__Type ->
  sL_TrafficPatternInfo_r16__trafficPeriodicity_r16__Type * (int * (sL_TrafficPatternInfo_r16__messageSize_r16__Type * (sL_QoS_FlowIdentity_r16__Type * unit)))

val sL_TrafficPatternInfo_r16__F2 : seq_type -> sL_TrafficPatternInfo_r16__Type

val sL_TrafficPatternInfo_r16__Format :
  sL_TrafficPatternInfo_r16__Type t_Format

type sL_UE_AssistanceInformationNR_r16__Type =
  sL_TrafficPatternInfo_r16__Type list

val sL_UE_AssistanceInformationNR_r16__Format :
  sL_UE_AssistanceInformationNR_r16__Type t_Format

type uL_GapFR2_Preference_r17__Type = { uL_GapFR2_Preference_r17__ul_GapFR2_PatternPreference_r17 : 
                                        int option }

val uL_GapFR2_Preference_r17__list : seq_elem list

val uL_GapFR2_Preference_r17__ul_GapFR2_PatternPreference_r17__Format :
  int t_Format

type uL_GapFR2_Preference_r17__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val uL_GapFR2_Preference_r17__Format_list :
  uL_GapFR2_Preference_r17__Format_Type

val uL_GapFR2_Preference_r17__list__Format : seq_type t_Format

val uL_GapFR2_Preference_r17__F1 :
  uL_GapFR2_Preference_r17__Type -> int option * unit

val uL_GapFR2_Preference_r17__F2 : seq_type -> uL_GapFR2_Preference_r17__Type

val uL_GapFR2_Preference_r17__Format : uL_GapFR2_Preference_r17__Type t_Format

type mUSIM_Starting_SFN_AndSubframe_r17__Type = { mUSIM_Starting_SFN_AndSubframe_r17__starting_SFN_r17 : 
                                                  int;
                                                  mUSIM_Starting_SFN_AndSubframe_r17__startingSubframe_r17 : 
                                                  int }

val mUSIM_Starting_SFN_AndSubframe_r17__list : seq_elem list

val mUSIM_Starting_SFN_AndSubframe_r17__starting_SFN_r17__Format : int t_Format

val mUSIM_Starting_SFN_AndSubframe_r17__startingSubframe_r17__Format :
  int t_Format

type mUSIM_Starting_SFN_AndSubframe_r17__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val mUSIM_Starting_SFN_AndSubframe_r17__Format_list :
  mUSIM_Starting_SFN_AndSubframe_r17__Format_Type

val mUSIM_Starting_SFN_AndSubframe_r17__list__Format : seq_type t_Format

val mUSIM_Starting_SFN_AndSubframe_r17__F1 :
  mUSIM_Starting_SFN_AndSubframe_r17__Type -> int * (int * unit)

val mUSIM_Starting_SFN_AndSubframe_r17__F2 :
  seq_type -> mUSIM_Starting_SFN_AndSubframe_r17__Type

val mUSIM_Starting_SFN_AndSubframe_r17__Format :
  mUSIM_Starting_SFN_AndSubframe_r17__Type t_Format

type mUSIM_GapInfo_r17__musim_GapLength_r17__Type =
| MUSIM_GapInfo_r17__musim_GapLength_r17__ms3
| MUSIM_GapInfo_r17__musim_GapLength_r17__ms4
| MUSIM_GapInfo_r17__musim_GapLength_r17__ms6
| MUSIM_GapInfo_r17__musim_GapLength_r17__ms10
| MUSIM_GapInfo_r17__musim_GapLength_r17__ms20

val mUSIM_GapInfo_r17__musim_GapLength_r17__nat__Format : int t_Format

val mUSIM_GapInfo_r17__musim_GapLength_r17__F1 :
  mUSIM_GapInfo_r17__musim_GapLength_r17__Type -> int

val mUSIM_GapInfo_r17__musim_GapLength_r17__F2 :
  int -> mUSIM_GapInfo_r17__musim_GapLength_r17__Type

type mUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__Type =
| MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms20_r17 of int
| MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms40_r17 of int
| MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms80_r17 of int
| MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms160_r17 of int
| MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms320_r17 of int
| MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms640_r17 of int
| MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms1280_r17 of int
| MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms2560_r17 of int
| MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms5120_r17 of int

type mUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__ext__Type = empty_set

type mUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__Type =
  (mUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__Type,
  mUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__ext__Type) sum

type mUSIM_GapInfo_r17__Type = { mUSIM_GapInfo_r17__musim_Starting_SFN_AndSubframe_r17 : 
                                 mUSIM_Starting_SFN_AndSubframe_r17__Type
                                 option;
                                 mUSIM_GapInfo_r17__musim_GapLength_r17 : 
                                 mUSIM_GapInfo_r17__musim_GapLength_r17__Type
                                 option;
                                 mUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17 : 
                                 mUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__Type
                                 option }

val mUSIM_GapInfo_r17__list : seq_elem list

val mUSIM_GapInfo_r17__musim_GapLength_r17__Format :
  mUSIM_GapInfo_r17__musim_GapLength_r17__Type t_Format

val mUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms20_r17__Format :
  int t_Format

val mUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms40_r17__Format :
  int t_Format

val mUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms80_r17__Format :
  int t_Format

val mUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms160_r17__Format :
  int t_Format

val mUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms320_r17__Format :
  int t_Format

val mUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms640_r17__Format :
  int t_Format

val mUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms1280_r17__Format :
  int t_Format

val mUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms2560_r17__Format :
  int t_Format

val mUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms5120_r17__Format :
  int t_Format

val mUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__list__Format :
  (int, __) sigT t_Format

val mUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__F1 :
  mUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__Type -> choice

val mUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__F2 :
  choice -> mUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__Type

val mUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__Format :
  mUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__Type t_Format

val mUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__ext__Format :
  mUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__ext__Type t_Format

val mUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__Format :
  mUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__Type t_Format

type mUSIM_GapInfo_r17__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val mUSIM_GapInfo_r17__Format_list : mUSIM_GapInfo_r17__Format_Type

val mUSIM_GapInfo_r17__list__Format : seq_type t_Format

val mUSIM_GapInfo_r17__F1 :
  mUSIM_GapInfo_r17__Type -> mUSIM_Starting_SFN_AndSubframe_r17__Type
  option * (mUSIM_GapInfo_r17__musim_GapLength_r17__Type
  option * (mUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__Type
  option * unit))

val mUSIM_GapInfo_r17__F2 : seq_type -> mUSIM_GapInfo_r17__Type

val mUSIM_GapInfo_r17__Format : mUSIM_GapInfo_r17__Type t_Format

type mUSIM_GapPreferenceList_r17__Type = mUSIM_GapInfo_r17__Type list

val mUSIM_GapPreferenceList_r17__Format :
  mUSIM_GapPreferenceList_r17__Type t_Format

type mUSIM_Assistance_r17__musim_PreferredRRC_State_r17__Type =
| MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__idle
| MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__inactive
| MUSIM_Assistance_r17__musim_PreferredRRC_State_r17__outOfConnected

val mUSIM_Assistance_r17__musim_PreferredRRC_State_r17__nat__Format :
  int t_Format

val mUSIM_Assistance_r17__musim_PreferredRRC_State_r17__F1 :
  mUSIM_Assistance_r17__musim_PreferredRRC_State_r17__Type -> int

val mUSIM_Assistance_r17__musim_PreferredRRC_State_r17__F2 :
  int -> mUSIM_Assistance_r17__musim_PreferredRRC_State_r17__Type

type mUSIM_Assistance_r17__Type = { mUSIM_Assistance_r17__musim_PreferredRRC_State_r17 : 
                                    mUSIM_Assistance_r17__musim_PreferredRRC_State_r17__Type
                                    option;
                                    mUSIM_Assistance_r17__musim_GapPreferenceList_r17 : 
                                    mUSIM_GapPreferenceList_r17__Type option }

val mUSIM_Assistance_r17__list : seq_elem list

val mUSIM_Assistance_r17__musim_PreferredRRC_State_r17__Format :
  mUSIM_Assistance_r17__musim_PreferredRRC_State_r17__Type t_Format

type mUSIM_Assistance_r17__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val mUSIM_Assistance_r17__Format_list : mUSIM_Assistance_r17__Format_Type

val mUSIM_Assistance_r17__list__Format : seq_type t_Format

val mUSIM_Assistance_r17__F1 :
  mUSIM_Assistance_r17__Type ->
  mUSIM_Assistance_r17__musim_PreferredRRC_State_r17__Type
  option * (mUSIM_GapPreferenceList_r17__Type option * unit)

val mUSIM_Assistance_r17__F2 : seq_type -> mUSIM_Assistance_r17__Type

val mUSIM_Assistance_r17__Format : mUSIM_Assistance_r17__Type t_Format

type reducedAggregatedBandwidth_r17__Type =
| ReducedAggregatedBandwidth_r17__mhz0
| ReducedAggregatedBandwidth_r17__mhz100
| ReducedAggregatedBandwidth_r17__mhz200
| ReducedAggregatedBandwidth_r17__mhz400
| ReducedAggregatedBandwidth_r17__mhz800
| ReducedAggregatedBandwidth_r17__mhz1200
| ReducedAggregatedBandwidth_r17__mhz1600
| ReducedAggregatedBandwidth_r17__mhz2000

val reducedAggregatedBandwidth_r17__nat__Format : int t_Format

val reducedAggregatedBandwidth_r17__F1 :
  reducedAggregatedBandwidth_r17__Type -> int

val reducedAggregatedBandwidth_r17__F2 :
  int -> reducedAggregatedBandwidth_r17__Type

val reducedAggregatedBandwidth_r17__Format :
  reducedAggregatedBandwidth_r17__Type t_Format

type overheatingAssistance_r17__reducedMaxBW_FR2_2_r17__Type = { overheatingAssistance_r17__reducedMaxBW_FR2_2_r17__reducedBW_FR2_2_DL_r17 : 
                                                                 reducedAggregatedBandwidth_r17__Type;
                                                                 overheatingAssistance_r17__reducedMaxBW_FR2_2_r17__reducedBW_FR2_2_UL_r17 : 
                                                                 reducedAggregatedBandwidth_r17__Type }

val overheatingAssistance_r17__reducedMaxBW_FR2_2_r17__list : seq_elem list

type overheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__Type = { overheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__reducedMIMO_LayersFR2_2_DL : 
                                                                     mIMO_LayersDL__Type;
                                                                     overheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__reducedMIMO_LayersFR2_2_UL : 
                                                                     mIMO_LayersUL__Type }

val overheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__list : seq_elem list

type overheatingAssistance_r17__Type = { overheatingAssistance_r17__reducedMaxBW_FR2_2_r17 : 
                                         overheatingAssistance_r17__reducedMaxBW_FR2_2_r17__Type
                                         option;
                                         overheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2 : 
                                         overheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__Type
                                         option }

val overheatingAssistance_r17__list : seq_elem list

type overheatingAssistance_r17__reducedMaxBW_FR2_2_r17__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val overheatingAssistance_r17__reducedMaxBW_FR2_2_r17__Format_list :
  overheatingAssistance_r17__reducedMaxBW_FR2_2_r17__Format_Type

val overheatingAssistance_r17__reducedMaxBW_FR2_2_r17__list__Format :
  seq_type t_Format

val overheatingAssistance_r17__reducedMaxBW_FR2_2_r17__F1 :
  overheatingAssistance_r17__reducedMaxBW_FR2_2_r17__Type ->
  reducedAggregatedBandwidth_r17__Type * (reducedAggregatedBandwidth_r17__Type * unit)

val overheatingAssistance_r17__reducedMaxBW_FR2_2_r17__F2 :
  seq_type -> overheatingAssistance_r17__reducedMaxBW_FR2_2_r17__Type

val overheatingAssistance_r17__reducedMaxBW_FR2_2_r17__Format :
  overheatingAssistance_r17__reducedMaxBW_FR2_2_r17__Type t_Format

type overheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val overheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__Format_list :
  overheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__Format_Type

val overheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__list__Format :
  seq_type t_Format

val overheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__F1 :
  overheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__Type ->
  mIMO_LayersDL__Type * (mIMO_LayersUL__Type * unit)

val overheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__F2 :
  seq_type -> overheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__Type

val overheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__Format :
  overheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__Type t_Format

type overheatingAssistance_r17__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val overheatingAssistance_r17__Format_list :
  overheatingAssistance_r17__Format_Type

val overheatingAssistance_r17__list__Format : seq_type t_Format

val overheatingAssistance_r17__F1 :
  overheatingAssistance_r17__Type ->
  overheatingAssistance_r17__reducedMaxBW_FR2_2_r17__Type
  option * (overheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__Type
  option * unit)

val overheatingAssistance_r17__F2 : seq_type -> overheatingAssistance_r17__Type

val overheatingAssistance_r17__Format :
  overheatingAssistance_r17__Type t_Format

type maxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__Type = { maxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__reducedBW_FR2_2_DL_r17 : 
                                                                 reducedAggregatedBandwidth_r17__Type
                                                                 option;
                                                                 maxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__reducedBW_FR2_2_UL_r17 : 
                                                                 reducedAggregatedBandwidth_r17__Type
                                                                 option }

val maxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__list : seq_elem list

type maxBW_PreferenceFR2_2_r17__Type = { maxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17 : 
                                         maxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__Type
                                         option }

val maxBW_PreferenceFR2_2_r17__list : seq_elem list

type maxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val maxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__Format_list :
  maxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__Format_Type

val maxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__list__Format :
  seq_type t_Format

val maxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__F1 :
  maxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__Type ->
  reducedAggregatedBandwidth_r17__Type
  option * (reducedAggregatedBandwidth_r17__Type option * unit)

val maxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__F2 :
  seq_type -> maxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__Type

val maxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__Format :
  maxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__Type t_Format

type maxBW_PreferenceFR2_2_r17__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val maxBW_PreferenceFR2_2_r17__Format_list :
  maxBW_PreferenceFR2_2_r17__Format_Type

val maxBW_PreferenceFR2_2_r17__list__Format : seq_type t_Format

val maxBW_PreferenceFR2_2_r17__F1 :
  maxBW_PreferenceFR2_2_r17__Type ->
  maxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__Type option * unit

val maxBW_PreferenceFR2_2_r17__F2 : seq_type -> maxBW_PreferenceFR2_2_r17__Type

val maxBW_PreferenceFR2_2_r17__Format :
  maxBW_PreferenceFR2_2_r17__Type t_Format

type maxMIMO_LayerPreferenceFR2_2_r17__reducedMaxMIMO_LayersFR2_2_r17__Type = { 
maxMIMO_LayerPreferenceFR2_2_r17__reducedMaxMIMO_LayersFR2_2_r17__reducedMIMO_LayersFR2_2_DL_r17 : 
int;
maxMIMO_LayerPreferenceFR2_2_r17__reducedMaxMIMO_LayersFR2_2_r17__reducedMIMO_LayersFR2_2_UL_r17 : 
int }

val maxMIMO_LayerPreferenceFR2_2_r17__reducedMaxMIMO_LayersFR2_2_r17__list :
  seq_elem list

type maxMIMO_LayerPreferenceFR2_2_r17__Type = { maxMIMO_LayerPreferenceFR2_2_r17__reducedMaxMIMO_LayersFR2_2_r17 : 
                                                maxMIMO_LayerPreferenceFR2_2_r17__reducedMaxMIMO_LayersFR2_2_r17__Type
                                                option }

val maxMIMO_LayerPreferenceFR2_2_r17__list : seq_elem list

val maxMIMO_LayerPreferenceFR2_2_r17__reducedMaxMIMO_LayersFR2_2_r17__reducedMIMO_LayersFR2_2_DL_r17__Format :
  int t_Format

val maxMIMO_LayerPreferenceFR2_2_r17__reducedMaxMIMO_LayersFR2_2_r17__reducedMIMO_LayersFR2_2_UL_r17__Format :
  int t_Format

type maxMIMO_LayerPreferenceFR2_2_r17__reducedMaxMIMO_LayersFR2_2_r17__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val maxMIMO_LayerPreferenceFR2_2_r17__reducedMaxMIMO_LayersFR2_2_r17__Format_list :
  maxMIMO_LayerPreferenceFR2_2_r17__reducedMaxMIMO_LayersFR2_2_r17__Format_Type

val maxMIMO_LayerPreferenceFR2_2_r17__reducedMaxMIMO_LayersFR2_2_r17__list__Format :
  seq_type t_Format

val maxMIMO_LayerPreferenceFR2_2_r17__reducedMaxMIMO_LayersFR2_2_r17__F1 :
  maxMIMO_LayerPreferenceFR2_2_r17__reducedMaxMIMO_LayersFR2_2_r17__Type ->
  int * (int * unit)

val maxMIMO_LayerPreferenceFR2_2_r17__reducedMaxMIMO_LayersFR2_2_r17__F2 :
  seq_type ->
  maxMIMO_LayerPreferenceFR2_2_r17__reducedMaxMIMO_LayersFR2_2_r17__Type

val maxMIMO_LayerPreferenceFR2_2_r17__reducedMaxMIMO_LayersFR2_2_r17__Format :
  maxMIMO_LayerPreferenceFR2_2_r17__reducedMaxMIMO_LayersFR2_2_r17__Type
  t_Format

type maxMIMO_LayerPreferenceFR2_2_r17__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val maxMIMO_LayerPreferenceFR2_2_r17__Format_list :
  maxMIMO_LayerPreferenceFR2_2_r17__Format_Type

val maxMIMO_LayerPreferenceFR2_2_r17__list__Format : seq_type t_Format

val maxMIMO_LayerPreferenceFR2_2_r17__F1 :
  maxMIMO_LayerPreferenceFR2_2_r17__Type ->
  maxMIMO_LayerPreferenceFR2_2_r17__reducedMaxMIMO_LayersFR2_2_r17__Type
  option * unit

val maxMIMO_LayerPreferenceFR2_2_r17__F2 :
  seq_type -> maxMIMO_LayerPreferenceFR2_2_r17__Type

val maxMIMO_LayerPreferenceFR2_2_r17__Format :
  maxMIMO_LayerPreferenceFR2_2_r17__Type t_Format

type minSchedulingOffsetPreferenceExt_r17__preferredK0_r17__preferredK0_SCS_480kHz_r17__Type =
| MinSchedulingOffsetPreferenceExt_r17__preferredK0_r17__preferredK0_SCS_480kHz_r17__sl8
| MinSchedulingOffsetPreferenceExt_r17__preferredK0_r17__preferredK0_SCS_480kHz_r17__sl16
| MinSchedulingOffsetPreferenceExt_r17__preferredK0_r17__preferredK0_SCS_480kHz_r17__sl32
| MinSchedulingOffsetPreferenceExt_r17__preferredK0_r17__preferredK0_SCS_480kHz_r17__sl48

val minSchedulingOffsetPreferenceExt_r17__preferredK0_r17__preferredK0_SCS_480kHz_r17__nat__Format :
  int t_Format

val minSchedulingOffsetPreferenceExt_r17__preferredK0_r17__preferredK0_SCS_480kHz_r17__F1 :
  minSchedulingOffsetPreferenceExt_r17__preferredK0_r17__preferredK0_SCS_480kHz_r17__Type
  -> int

val minSchedulingOffsetPreferenceExt_r17__preferredK0_r17__preferredK0_SCS_480kHz_r17__F2 :
  int ->
  minSchedulingOffsetPreferenceExt_r17__preferredK0_r17__preferredK0_SCS_480kHz_r17__Type

type minSchedulingOffsetPreferenceExt_r17__preferredK0_r17__preferredK0_SCS_960kHz_r17__Type =
| MinSchedulingOffsetPreferenceExt_r17__preferredK0_r17__preferredK0_SCS_960kHz_r17__sl8
| MinSchedulingOffsetPreferenceExt_r17__preferredK0_r17__preferredK0_SCS_960kHz_r17__sl16
| MinSchedulingOffsetPreferenceExt_r17__preferredK0_r17__preferredK0_SCS_960kHz_r17__sl32
| MinSchedulingOffsetPreferenceExt_r17__preferredK0_r17__preferredK0_SCS_960kHz_r17__sl48

val minSchedulingOffsetPreferenceExt_r17__preferredK0_r17__preferredK0_SCS_960kHz_r17__nat__Format :
  int t_Format

val minSchedulingOffsetPreferenceExt_r17__preferredK0_r17__preferredK0_SCS_960kHz_r17__F1 :
  minSchedulingOffsetPreferenceExt_r17__preferredK0_r17__preferredK0_SCS_960kHz_r17__Type
  -> int

val minSchedulingOffsetPreferenceExt_r17__preferredK0_r17__preferredK0_SCS_960kHz_r17__F2 :
  int ->
  minSchedulingOffsetPreferenceExt_r17__preferredK0_r17__preferredK0_SCS_960kHz_r17__Type

type minSchedulingOffsetPreferenceExt_r17__preferredK0_r17__Type = { minSchedulingOffsetPreferenceExt_r17__preferredK0_r17__preferredK0_SCS_480kHz_r17 : 
                                                                     minSchedulingOffsetPreferenceExt_r17__preferredK0_r17__preferredK0_SCS_480kHz_r17__Type
                                                                     option;
                                                                     minSchedulingOffsetPreferenceExt_r17__preferredK0_r17__preferredK0_SCS_960kHz_r17 : 
                                                                     minSchedulingOffsetPreferenceExt_r17__preferredK0_r17__preferredK0_SCS_960kHz_r17__Type
                                                                     option }

val minSchedulingOffsetPreferenceExt_r17__preferredK0_r17__list : seq_elem list

type minSchedulingOffsetPreferenceExt_r17__preferredK2_r17__preferredK2_SCS_480kHz_r17__Type =
| MinSchedulingOffsetPreferenceExt_r17__preferredK2_r17__preferredK2_SCS_480kHz_r17__sl8
| MinSchedulingOffsetPreferenceExt_r17__preferredK2_r17__preferredK2_SCS_480kHz_r17__sl16
| MinSchedulingOffsetPreferenceExt_r17__preferredK2_r17__preferredK2_SCS_480kHz_r17__sl32
| MinSchedulingOffsetPreferenceExt_r17__preferredK2_r17__preferredK2_SCS_480kHz_r17__sl48

val minSchedulingOffsetPreferenceExt_r17__preferredK2_r17__preferredK2_SCS_480kHz_r17__nat__Format :
  int t_Format

val minSchedulingOffsetPreferenceExt_r17__preferredK2_r17__preferredK2_SCS_480kHz_r17__F1 :
  minSchedulingOffsetPreferenceExt_r17__preferredK2_r17__preferredK2_SCS_480kHz_r17__Type
  -> int

val minSchedulingOffsetPreferenceExt_r17__preferredK2_r17__preferredK2_SCS_480kHz_r17__F2 :
  int ->
  minSchedulingOffsetPreferenceExt_r17__preferredK2_r17__preferredK2_SCS_480kHz_r17__Type

type minSchedulingOffsetPreferenceExt_r17__preferredK2_r17__preferredK2_SCS_960kHz_r17__Type =
| MinSchedulingOffsetPreferenceExt_r17__preferredK2_r17__preferredK2_SCS_960kHz_r17__sl8
| MinSchedulingOffsetPreferenceExt_r17__preferredK2_r17__preferredK2_SCS_960kHz_r17__sl16
| MinSchedulingOffsetPreferenceExt_r17__preferredK2_r17__preferredK2_SCS_960kHz_r17__sl32
| MinSchedulingOffsetPreferenceExt_r17__preferredK2_r17__preferredK2_SCS_960kHz_r17__sl48

val minSchedulingOffsetPreferenceExt_r17__preferredK2_r17__preferredK2_SCS_960kHz_r17__nat__Format :
  int t_Format

val minSchedulingOffsetPreferenceExt_r17__preferredK2_r17__preferredK2_SCS_960kHz_r17__F1 :
  minSchedulingOffsetPreferenceExt_r17__preferredK2_r17__preferredK2_SCS_960kHz_r17__Type
  -> int

val minSchedulingOffsetPreferenceExt_r17__preferredK2_r17__preferredK2_SCS_960kHz_r17__F2 :
  int ->
  minSchedulingOffsetPreferenceExt_r17__preferredK2_r17__preferredK2_SCS_960kHz_r17__Type

type minSchedulingOffsetPreferenceExt_r17__preferredK2_r17__Type = { minSchedulingOffsetPreferenceExt_r17__preferredK2_r17__preferredK2_SCS_480kHz_r17 : 
                                                                     minSchedulingOffsetPreferenceExt_r17__preferredK2_r17__preferredK2_SCS_480kHz_r17__Type
                                                                     option;
                                                                     minSchedulingOffsetPreferenceExt_r17__preferredK2_r17__preferredK2_SCS_960kHz_r17 : 
                                                                     minSchedulingOffsetPreferenceExt_r17__preferredK2_r17__preferredK2_SCS_960kHz_r17__Type
                                                                     option }

val minSchedulingOffsetPreferenceExt_r17__preferredK2_r17__list : seq_elem list

type minSchedulingOffsetPreferenceExt_r17__Type = { minSchedulingOffsetPreferenceExt_r17__preferredK0_r17 : 
                                                    minSchedulingOffsetPreferenceExt_r17__preferredK0_r17__Type
                                                    option;
                                                    minSchedulingOffsetPreferenceExt_r17__preferredK2_r17 : 
                                                    minSchedulingOffsetPreferenceExt_r17__preferredK2_r17__Type
                                                    option }

val minSchedulingOffsetPreferenceExt_r17__list : seq_elem list

val minSchedulingOffsetPreferenceExt_r17__preferredK0_r17__preferredK0_SCS_480kHz_r17__Format :
  minSchedulingOffsetPreferenceExt_r17__preferredK0_r17__preferredK0_SCS_480kHz_r17__Type
  t_Format

val minSchedulingOffsetPreferenceExt_r17__preferredK0_r17__preferredK0_SCS_960kHz_r17__Format :
  minSchedulingOffsetPreferenceExt_r17__preferredK0_r17__preferredK0_SCS_960kHz_r17__Type
  t_Format

type minSchedulingOffsetPreferenceExt_r17__preferredK0_r17__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val minSchedulingOffsetPreferenceExt_r17__preferredK0_r17__Format_list :
  minSchedulingOffsetPreferenceExt_r17__preferredK0_r17__Format_Type

val minSchedulingOffsetPreferenceExt_r17__preferredK0_r17__list__Format :
  seq_type t_Format

val minSchedulingOffsetPreferenceExt_r17__preferredK0_r17__F1 :
  minSchedulingOffsetPreferenceExt_r17__preferredK0_r17__Type ->
  minSchedulingOffsetPreferenceExt_r17__preferredK0_r17__preferredK0_SCS_480kHz_r17__Type
  option * (minSchedulingOffsetPreferenceExt_r17__preferredK0_r17__preferredK0_SCS_960kHz_r17__Type
  option * unit)

val minSchedulingOffsetPreferenceExt_r17__preferredK0_r17__F2 :
  seq_type -> minSchedulingOffsetPreferenceExt_r17__preferredK0_r17__Type

val minSchedulingOffsetPreferenceExt_r17__preferredK0_r17__Format :
  minSchedulingOffsetPreferenceExt_r17__preferredK0_r17__Type t_Format

val minSchedulingOffsetPreferenceExt_r17__preferredK2_r17__preferredK2_SCS_480kHz_r17__Format :
  minSchedulingOffsetPreferenceExt_r17__preferredK2_r17__preferredK2_SCS_480kHz_r17__Type
  t_Format

val minSchedulingOffsetPreferenceExt_r17__preferredK2_r17__preferredK2_SCS_960kHz_r17__Format :
  minSchedulingOffsetPreferenceExt_r17__preferredK2_r17__preferredK2_SCS_960kHz_r17__Type
  t_Format

type minSchedulingOffsetPreferenceExt_r17__preferredK2_r17__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val minSchedulingOffsetPreferenceExt_r17__preferredK2_r17__Format_list :
  minSchedulingOffsetPreferenceExt_r17__preferredK2_r17__Format_Type

val minSchedulingOffsetPreferenceExt_r17__preferredK2_r17__list__Format :
  seq_type t_Format

val minSchedulingOffsetPreferenceExt_r17__preferredK2_r17__F1 :
  minSchedulingOffsetPreferenceExt_r17__preferredK2_r17__Type ->
  minSchedulingOffsetPreferenceExt_r17__preferredK2_r17__preferredK2_SCS_480kHz_r17__Type
  option * (minSchedulingOffsetPreferenceExt_r17__preferredK2_r17__preferredK2_SCS_960kHz_r17__Type
  option * unit)

val minSchedulingOffsetPreferenceExt_r17__preferredK2_r17__F2 :
  seq_type -> minSchedulingOffsetPreferenceExt_r17__preferredK2_r17__Type

val minSchedulingOffsetPreferenceExt_r17__preferredK2_r17__Format :
  minSchedulingOffsetPreferenceExt_r17__preferredK2_r17__Type t_Format

type minSchedulingOffsetPreferenceExt_r17__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val minSchedulingOffsetPreferenceExt_r17__Format_list :
  minSchedulingOffsetPreferenceExt_r17__Format_Type

val minSchedulingOffsetPreferenceExt_r17__list__Format : seq_type t_Format

val minSchedulingOffsetPreferenceExt_r17__F1 :
  minSchedulingOffsetPreferenceExt_r17__Type ->
  minSchedulingOffsetPreferenceExt_r17__preferredK0_r17__Type
  option * (minSchedulingOffsetPreferenceExt_r17__preferredK2_r17__Type
  option * unit)

val minSchedulingOffsetPreferenceExt_r17__F2 :
  seq_type -> minSchedulingOffsetPreferenceExt_r17__Type

val minSchedulingOffsetPreferenceExt_r17__Format :
  minSchedulingOffsetPreferenceExt_r17__Type t_Format

type resumeCause__Type =
| ResumeCause__emergency
| ResumeCause__highPriorityAccess
| ResumeCause__mt_Access
| ResumeCause__mo_Signalling
| ResumeCause__mo_Data
| ResumeCause__mo_VoiceCall
| ResumeCause__mo_VideoCall
| ResumeCause__mo_SMS
| ResumeCause__rna_Update
| ResumeCause__mps_PriorityAccess
| ResumeCause__mcs_PriorityAccess
| ResumeCause__spare1
| ResumeCause__spare2
| ResumeCause__spare3
| ResumeCause__spare4
| ResumeCause__spare5

val resumeCause__nat__Format : int t_Format

val resumeCause__F1 : resumeCause__Type -> int

val resumeCause__F2 : int -> resumeCause__Type

val resumeCause__Format : resumeCause__Type t_Format

type propagationDelayDifference_r17__Type = int list

val propagationDelayDifference_r17__seq_of__Format : int t_Format

val propagationDelayDifference_r17__Format :
  propagationDelayDifference_r17__Type t_Format

type uEAssistanceInformation_v1700_IEs__bfd_MeasRelaxationState_r17__Type =
  bit_string

type uEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__Type = { 
uEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__resumeCause_r17 : 
resumeCause__Type option }

val uEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__list :
  seq_elem list

type uEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__Type =
| UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__scgDeactivationPreferred
| UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__noPreference

val uEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__nat__Format :
  int t_Format

val uEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__F1 :
  uEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__Type ->
  int

val uEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__F2 :
  int ->
  uEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__Type

type uEAssistanceInformation_v1700_IEs__uplinkData_r17__Type =
| UEAssistanceInformation_v1700_IEs__uplinkData_r17__true

val uEAssistanceInformation_v1700_IEs__uplinkData_r17__nat__Format :
  int t_Format

val uEAssistanceInformation_v1700_IEs__uplinkData_r17__F1 :
  uEAssistanceInformation_v1700_IEs__uplinkData_r17__Type -> int

val uEAssistanceInformation_v1700_IEs__uplinkData_r17__F2 :
  int -> uEAssistanceInformation_v1700_IEs__uplinkData_r17__Type

type uEAssistanceInformation_v1700_IEs__nonCriticalExtension__Type =
| Make__UEAssistanceInformation_v1700_IEs__nonCriticalExtension__Type

type uEAssistanceInformation_v1700_IEs__Type = { uEAssistanceInformation_v1700_IEs__ul_GapFR2_Preference_r17 : 
                                                 uL_GapFR2_Preference_r17__Type
                                                 option;
                                                 uEAssistanceInformation_v1700_IEs__musim_Assistance_r17 : 
                                                 mUSIM_Assistance_r17__Type
                                                 option;
                                                 uEAssistanceInformation_v1700_IEs__overheatingAssistance_r17 : 
                                                 overheatingAssistance_r17__Type
                                                 option;
                                                 uEAssistanceInformation_v1700_IEs__maxBW_PreferenceFR2_2_r17 : 
                                                 maxBW_PreferenceFR2_2_r17__Type
                                                 option;
                                                 uEAssistanceInformation_v1700_IEs__maxMIMO_LayerPreferenceFR2_2_r17 : 
                                                 maxMIMO_LayerPreferenceFR2_2_r17__Type
                                                 option;
                                                 uEAssistanceInformation_v1700_IEs__minSchedulingOffsetPreferenceExt_r17 : 
                                                 minSchedulingOffsetPreferenceExt_r17__Type
                                                 option;
                                                 uEAssistanceInformation_v1700_IEs__rlm_MeasRelaxationState_r17 : 
                                                 bool option;
                                                 uEAssistanceInformation_v1700_IEs__bfd_MeasRelaxationState_r17 : 
                                                 uEAssistanceInformation_v1700_IEs__bfd_MeasRelaxationState_r17__Type
                                                 option;
                                                 uEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17 : 
                                                 uEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__Type
                                                 option;
                                                 uEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17 : 
                                                 uEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__Type
                                                 option;
                                                 uEAssistanceInformation_v1700_IEs__uplinkData_r17 : 
                                                 uEAssistanceInformation_v1700_IEs__uplinkData_r17__Type
                                                 option;
                                                 uEAssistanceInformation_v1700_IEs__rrm_MeasRelaxationFulfilment_r17 : 
                                                 bool option;
                                                 uEAssistanceInformation_v1700_IEs__propagationDelayDifference_r17 : 
                                                 propagationDelayDifference_r17__Type
                                                 option;
                                                 uEAssistanceInformation_v1700_IEs__nonCriticalExtension : 
                                                 uEAssistanceInformation_v1700_IEs__nonCriticalExtension__Type
                                                 option }

val uEAssistanceInformation_v1700_IEs__list : seq_elem list

val uEAssistanceInformation_v1700_IEs__bfd_MeasRelaxationState_r17__Format :
  uEAssistanceInformation_v1700_IEs__bfd_MeasRelaxationState_r17__Type t_Format

type uEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val uEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__Format_list :
  uEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__Format_Type

val uEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__list__Format :
  seq_type t_Format

val uEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__F1 :
  uEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__Type ->
  resumeCause__Type option * unit

val uEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__F2 :
  seq_type ->
  uEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__Type

val uEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__Format :
  uEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__Type t_Format

val uEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__Format :
  uEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__Type
  t_Format

val uEAssistanceInformation_v1700_IEs__uplinkData_r17__Format :
  uEAssistanceInformation_v1700_IEs__uplinkData_r17__Type t_Format

val uEAssistanceInformation_v1700_IEs__nonCriticalExtension__Format :
  uEAssistanceInformation_v1700_IEs__nonCriticalExtension__Type t_Format

type uEAssistanceInformation_v1700_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))))))))))))

val uEAssistanceInformation_v1700_IEs__Format_list :
  uEAssistanceInformation_v1700_IEs__Format_Type

val uEAssistanceInformation_v1700_IEs__list__Format : seq_type t_Format

val uEAssistanceInformation_v1700_IEs__F1 :
  uEAssistanceInformation_v1700_IEs__Type -> uL_GapFR2_Preference_r17__Type
  option * (mUSIM_Assistance_r17__Type
  option * (overheatingAssistance_r17__Type
  option * (maxBW_PreferenceFR2_2_r17__Type
  option * (maxMIMO_LayerPreferenceFR2_2_r17__Type
  option * (minSchedulingOffsetPreferenceExt_r17__Type option * (bool
  option * (uEAssistanceInformation_v1700_IEs__bfd_MeasRelaxationState_r17__Type
  option * (uEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__Type
  option * (uEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__Type
  option * (uEAssistanceInformation_v1700_IEs__uplinkData_r17__Type
  option * (bool option * (propagationDelayDifference_r17__Type
  option * (uEAssistanceInformation_v1700_IEs__nonCriticalExtension__Type
  option * unit)))))))))))))

val uEAssistanceInformation_v1700_IEs__F2 :
  seq_type -> uEAssistanceInformation_v1700_IEs__Type

val uEAssistanceInformation_v1700_IEs__Format :
  uEAssistanceInformation_v1700_IEs__Type t_Format

type uEAssistanceInformation_v1610_IEs__Type = { uEAssistanceInformation_v1610_IEs__idc_Assistance_r16 : 
                                                 iDC_Assistance_r16__Type
                                                 option;
                                                 uEAssistanceInformation_v1610_IEs__drx_Preference_r16 : 
                                                 dRX_Preference_r16__Type
                                                 option;
                                                 uEAssistanceInformation_v1610_IEs__maxBW_Preference_r16 : 
                                                 maxBW_Preference_r16__Type
                                                 option;
                                                 uEAssistanceInformation_v1610_IEs__maxCC_Preference_r16 : 
                                                 maxCC_Preference_r16__Type
                                                 option;
                                                 uEAssistanceInformation_v1610_IEs__maxMIMO_LayerPreference_r16 : 
                                                 maxMIMO_LayerPreference_r16__Type
                                                 option;
                                                 uEAssistanceInformation_v1610_IEs__minSchedulingOffsetPreference_r16 : 
                                                 minSchedulingOffsetPreference_r16__Type
                                                 option;
                                                 uEAssistanceInformation_v1610_IEs__releasePreference_r16 : 
                                                 releasePreference_r16__Type
                                                 option;
                                                 uEAssistanceInformation_v1610_IEs__sl_UE_AssistanceInformationNR_r16 : 
                                                 sL_UE_AssistanceInformationNR_r16__Type
                                                 option;
                                                 uEAssistanceInformation_v1610_IEs__referenceTimeInfoPreference_r16 : 
                                                 bool option;
                                                 uEAssistanceInformation_v1610_IEs__nonCriticalExtension : 
                                                 uEAssistanceInformation_v1700_IEs__Type
                                                 option }

val uEAssistanceInformation_v1610_IEs__list : seq_elem list

type uEAssistanceInformation_v1610_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))))))))

val uEAssistanceInformation_v1610_IEs__Format_list :
  uEAssistanceInformation_v1610_IEs__Format_Type

val uEAssistanceInformation_v1610_IEs__list__Format : seq_type t_Format

val uEAssistanceInformation_v1610_IEs__F1 :
  uEAssistanceInformation_v1610_IEs__Type -> iDC_Assistance_r16__Type
  option * (dRX_Preference_r16__Type option * (maxBW_Preference_r16__Type
  option * (maxCC_Preference_r16__Type
  option * (maxMIMO_LayerPreference_r16__Type
  option * (minSchedulingOffsetPreference_r16__Type
  option * (releasePreference_r16__Type
  option * (sL_UE_AssistanceInformationNR_r16__Type option * (bool
  option * (uEAssistanceInformation_v1700_IEs__Type option * unit)))))))))

val uEAssistanceInformation_v1610_IEs__F2 :
  seq_type -> uEAssistanceInformation_v1610_IEs__Type

val uEAssistanceInformation_v1610_IEs__Format :
  uEAssistanceInformation_v1610_IEs__Type t_Format

type uEAssistanceInformation_v1540_IEs__Type = { uEAssistanceInformation_v1540_IEs__overheatingAssistance : 
                                                 overheatingAssistance__Type
                                                 option;
                                                 uEAssistanceInformation_v1540_IEs__nonCriticalExtension : 
                                                 uEAssistanceInformation_v1610_IEs__Type
                                                 option }

val uEAssistanceInformation_v1540_IEs__list : seq_elem list

type uEAssistanceInformation_v1540_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val uEAssistanceInformation_v1540_IEs__Format_list :
  uEAssistanceInformation_v1540_IEs__Format_Type

val uEAssistanceInformation_v1540_IEs__list__Format : seq_type t_Format

val uEAssistanceInformation_v1540_IEs__F1 :
  uEAssistanceInformation_v1540_IEs__Type -> overheatingAssistance__Type
  option * (uEAssistanceInformation_v1610_IEs__Type option * unit)

val uEAssistanceInformation_v1540_IEs__F2 :
  seq_type -> uEAssistanceInformation_v1540_IEs__Type

val uEAssistanceInformation_v1540_IEs__Format :
  uEAssistanceInformation_v1540_IEs__Type t_Format

type uEAssistanceInformation_IEs__Type = { uEAssistanceInformation_IEs__delayBudgetReport : 
                                           delayBudgetReport__Type option;
                                           uEAssistanceInformation_IEs__lateNonCriticalExtension : 
                                           octet_string option;
                                           uEAssistanceInformation_IEs__nonCriticalExtension : 
                                           uEAssistanceInformation_v1540_IEs__Type
                                           option }

val uEAssistanceInformation_IEs__list : seq_elem list

type uEAssistanceInformation_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val uEAssistanceInformation_IEs__Format_list :
  uEAssistanceInformation_IEs__Format_Type

val uEAssistanceInformation_IEs__list__Format : seq_type t_Format

val uEAssistanceInformation_IEs__F1 :
  uEAssistanceInformation_IEs__Type -> delayBudgetReport__Type
  option * (octet_string option * (uEAssistanceInformation_v1540_IEs__Type
  option * unit))

val uEAssistanceInformation_IEs__F2 :
  seq_type -> uEAssistanceInformation_IEs__Type

val uEAssistanceInformation_IEs__Format :
  uEAssistanceInformation_IEs__Type t_Format

type uEAssistanceInformation__criticalExtensions__criticalExtensionsFuture__Type =
| Make__UEAssistanceInformation__criticalExtensions__criticalExtensionsFuture__Type

type uEAssistanceInformation__criticalExtensions__Type =
| UEAssistanceInformation__criticalExtensions__ueAssistanceInformation of 
   uEAssistanceInformation_IEs__Type
| UEAssistanceInformation__criticalExtensions__criticalExtensionsFuture of 
   uEAssistanceInformation__criticalExtensions__criticalExtensionsFuture__Type

type uEAssistanceInformation__Type = { uEAssistanceInformation__criticalExtensions : 
                                       uEAssistanceInformation__criticalExtensions__Type }

val uEAssistanceInformation__list : seq_elem list

val uEAssistanceInformation__criticalExtensions__criticalExtensionsFuture__Format :
  uEAssistanceInformation__criticalExtensions__criticalExtensionsFuture__Type
  t_Format

val uEAssistanceInformation__criticalExtensions__list__Format :
  (int, __) sigT t_Format

val uEAssistanceInformation__criticalExtensions__F1 :
  uEAssistanceInformation__criticalExtensions__Type -> choice

val uEAssistanceInformation__criticalExtensions__F2 :
  choice -> uEAssistanceInformation__criticalExtensions__Type

val uEAssistanceInformation__criticalExtensions__Format :
  uEAssistanceInformation__criticalExtensions__Type t_Format

type uEAssistanceInformation__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val uEAssistanceInformation__Format_list : uEAssistanceInformation__Format_Type

val uEAssistanceInformation__list__Format : seq_type t_Format

val uEAssistanceInformation__F1 :
  uEAssistanceInformation__Type ->
  uEAssistanceInformation__criticalExtensions__Type * unit

val uEAssistanceInformation__F2 : seq_type -> uEAssistanceInformation__Type

val uEAssistanceInformation__Format : uEAssistanceInformation__Type t_Format

type cellGroupId__Type = int

val cellGroupId__Format : int t_Format

type logicalChannelIdentity__Type = int

val logicalChannelIdentity__Format : int t_Format

type failureInfoRLC_Bearer__failureType__Type =
| FailureInfoRLC_Bearer__failureType__rlc_failure
| FailureInfoRLC_Bearer__failureType__spare3
| FailureInfoRLC_Bearer__failureType__spare2
| FailureInfoRLC_Bearer__failureType__spare1

val failureInfoRLC_Bearer__failureType__nat__Format : int t_Format

val failureInfoRLC_Bearer__failureType__F1 :
  failureInfoRLC_Bearer__failureType__Type -> int

val failureInfoRLC_Bearer__failureType__F2 :
  int -> failureInfoRLC_Bearer__failureType__Type

type failureInfoRLC_Bearer__Type = { failureInfoRLC_Bearer__cellGroupId : 
                                     cellGroupId__Type;
                                     failureInfoRLC_Bearer__logicalChannelIdentity : 
                                     logicalChannelIdentity__Type;
                                     failureInfoRLC_Bearer__failureType : 
                                     failureInfoRLC_Bearer__failureType__Type }

val failureInfoRLC_Bearer__list : seq_elem list

val failureInfoRLC_Bearer__failureType__Format :
  failureInfoRLC_Bearer__failureType__Type t_Format

type failureInfoRLC_Bearer__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val failureInfoRLC_Bearer__Format_list : failureInfoRLC_Bearer__Format_Type

val failureInfoRLC_Bearer__list__Format : seq_type t_Format

val failureInfoRLC_Bearer__F1 :
  failureInfoRLC_Bearer__Type ->
  cellGroupId__Type * (logicalChannelIdentity__Type * (failureInfoRLC_Bearer__failureType__Type * unit))

val failureInfoRLC_Bearer__F2 : seq_type -> failureInfoRLC_Bearer__Type

val failureInfoRLC_Bearer__Format : failureInfoRLC_Bearer__Type t_Format

type failureInfoDAPS_r16__failureType_r16__Type =
| FailureInfoDAPS_r16__failureType_r16__daps_failure
| FailureInfoDAPS_r16__failureType_r16__spare3
| FailureInfoDAPS_r16__failureType_r16__spare2
| FailureInfoDAPS_r16__failureType_r16__spare1

val failureInfoDAPS_r16__failureType_r16__nat__Format : int t_Format

val failureInfoDAPS_r16__failureType_r16__F1 :
  failureInfoDAPS_r16__failureType_r16__Type -> int

val failureInfoDAPS_r16__failureType_r16__F2 :
  int -> failureInfoDAPS_r16__failureType_r16__Type

type failureInfoDAPS_r16__Type = { failureInfoDAPS_r16__failureType_r16 : 
                                   failureInfoDAPS_r16__failureType_r16__Type }

val failureInfoDAPS_r16__list : seq_elem list

val failureInfoDAPS_r16__failureType_r16__Format :
  failureInfoDAPS_r16__failureType_r16__Type t_Format

type failureInfoDAPS_r16__Format_Type = seq_elem_to_format * seq_elem_to_format

val failureInfoDAPS_r16__Format_list : failureInfoDAPS_r16__Format_Type

val failureInfoDAPS_r16__list__Format : seq_type t_Format

val failureInfoDAPS_r16__F1 :
  failureInfoDAPS_r16__Type ->
  failureInfoDAPS_r16__failureType_r16__Type * unit

val failureInfoDAPS_r16__F2 : seq_type -> failureInfoDAPS_r16__Type

val failureInfoDAPS_r16__Format : failureInfoDAPS_r16__Type t_Format

type failureInformation_v1610_IEs__nonCriticalExtension__Type =
| Make__FailureInformation_v1610_IEs__nonCriticalExtension__Type

type failureInformation_v1610_IEs__Type = { failureInformation_v1610_IEs__failureInfoDAPS_r16 : 
                                            failureInfoDAPS_r16__Type option;
                                            failureInformation_v1610_IEs__nonCriticalExtension : 
                                            failureInformation_v1610_IEs__nonCriticalExtension__Type
                                            option }

val failureInformation_v1610_IEs__list : seq_elem list

val failureInformation_v1610_IEs__nonCriticalExtension__Format :
  failureInformation_v1610_IEs__nonCriticalExtension__Type t_Format

type failureInformation_v1610_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val failureInformation_v1610_IEs__Format_list :
  failureInformation_v1610_IEs__Format_Type

val failureInformation_v1610_IEs__list__Format : seq_type t_Format

val failureInformation_v1610_IEs__F1 :
  failureInformation_v1610_IEs__Type -> failureInfoDAPS_r16__Type
  option * (failureInformation_v1610_IEs__nonCriticalExtension__Type
  option * unit)

val failureInformation_v1610_IEs__F2 :
  seq_type -> failureInformation_v1610_IEs__Type

val failureInformation_v1610_IEs__Format :
  failureInformation_v1610_IEs__Type t_Format

type failureInformation_IEs__Type = { failureInformation_IEs__failureInfoRLC_Bearer : 
                                      failureInfoRLC_Bearer__Type option;
                                      failureInformation_IEs__lateNonCriticalExtension : 
                                      octet_string option;
                                      failureInformation_IEs__nonCriticalExtension : 
                                      failureInformation_v1610_IEs__Type option }

val failureInformation_IEs__list : seq_elem list

type failureInformation_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val failureInformation_IEs__Format_list : failureInformation_IEs__Format_Type

val failureInformation_IEs__list__Format : seq_type t_Format

val failureInformation_IEs__F1 :
  failureInformation_IEs__Type -> failureInfoRLC_Bearer__Type
  option * (octet_string option * (failureInformation_v1610_IEs__Type
  option * unit))

val failureInformation_IEs__F2 : seq_type -> failureInformation_IEs__Type

val failureInformation_IEs__Format : failureInformation_IEs__Type t_Format

type failureInformation__criticalExtensions__criticalExtensionsFuture__Type =
| Make__FailureInformation__criticalExtensions__criticalExtensionsFuture__Type

type failureInformation__criticalExtensions__Type =
| FailureInformation__criticalExtensions__failureInformation of failureInformation_IEs__Type
| FailureInformation__criticalExtensions__criticalExtensionsFuture of 
   failureInformation__criticalExtensions__criticalExtensionsFuture__Type

type failureInformation__Type = { failureInformation__criticalExtensions : 
                                  failureInformation__criticalExtensions__Type }

val failureInformation__list : seq_elem list

val failureInformation__criticalExtensions__criticalExtensionsFuture__Format :
  failureInformation__criticalExtensions__criticalExtensionsFuture__Type
  t_Format

val failureInformation__criticalExtensions__list__Format :
  (int, __) sigT t_Format

val failureInformation__criticalExtensions__F1 :
  failureInformation__criticalExtensions__Type -> choice

val failureInformation__criticalExtensions__F2 :
  choice -> failureInformation__criticalExtensions__Type

val failureInformation__criticalExtensions__Format :
  failureInformation__criticalExtensions__Type t_Format

type failureInformation__Format_Type = seq_elem_to_format * seq_elem_to_format

val failureInformation__Format_list : failureInformation__Format_Type

val failureInformation__list__Format : seq_type t_Format

val failureInformation__F1 :
  failureInformation__Type ->
  failureInformation__criticalExtensions__Type * unit

val failureInformation__F2 : seq_type -> failureInformation__Type

val failureInformation__Format : failureInformation__Type t_Format

type uLInformationTransferMRDC_IEs__nonCriticalExtension__Type =
| Make__ULInformationTransferMRDC_IEs__nonCriticalExtension__Type

type uLInformationTransferMRDC_IEs__Type = { uLInformationTransferMRDC_IEs__ul_DCCH_MessageNR : 
                                             octet_string option;
                                             uLInformationTransferMRDC_IEs__ul_DCCH_MessageEUTRA : 
                                             octet_string option;
                                             uLInformationTransferMRDC_IEs__lateNonCriticalExtension : 
                                             octet_string option;
                                             uLInformationTransferMRDC_IEs__nonCriticalExtension : 
                                             uLInformationTransferMRDC_IEs__nonCriticalExtension__Type
                                             option }

val uLInformationTransferMRDC_IEs__list : seq_elem list

val uLInformationTransferMRDC_IEs__nonCriticalExtension__Format :
  uLInformationTransferMRDC_IEs__nonCriticalExtension__Type t_Format

type uLInformationTransferMRDC_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

val uLInformationTransferMRDC_IEs__Format_list :
  uLInformationTransferMRDC_IEs__Format_Type

val uLInformationTransferMRDC_IEs__list__Format : seq_type t_Format

val uLInformationTransferMRDC_IEs__F1 :
  uLInformationTransferMRDC_IEs__Type -> octet_string option * (octet_string
  option * (octet_string
  option * (uLInformationTransferMRDC_IEs__nonCriticalExtension__Type
  option * unit)))

val uLInformationTransferMRDC_IEs__F2 :
  seq_type -> uLInformationTransferMRDC_IEs__Type

val uLInformationTransferMRDC_IEs__Format :
  uLInformationTransferMRDC_IEs__Type t_Format

type uLInformationTransferMRDC__criticalExtensions__c1__Type =
| ULInformationTransferMRDC__criticalExtensions__c1__ulInformationTransferMRDC of 
   uLInformationTransferMRDC_IEs__Type
| ULInformationTransferMRDC__criticalExtensions__c1__spare3 of unit
| ULInformationTransferMRDC__criticalExtensions__c1__spare2 of unit
| ULInformationTransferMRDC__criticalExtensions__c1__spare1 of unit

type uLInformationTransferMRDC__criticalExtensions__criticalExtensionsFuture__Type =
| Make__ULInformationTransferMRDC__criticalExtensions__criticalExtensionsFuture__Type

type uLInformationTransferMRDC__criticalExtensions__Type =
| ULInformationTransferMRDC__criticalExtensions__c1 of uLInformationTransferMRDC__criticalExtensions__c1__Type
| ULInformationTransferMRDC__criticalExtensions__criticalExtensionsFuture of 
   uLInformationTransferMRDC__criticalExtensions__criticalExtensionsFuture__Type

type uLInformationTransferMRDC__Type = { uLInformationTransferMRDC__criticalExtensions : 
                                         uLInformationTransferMRDC__criticalExtensions__Type }

val uLInformationTransferMRDC__list : seq_elem list

val uLInformationTransferMRDC__criticalExtensions__c1__list__Format :
  (int, __) sigT t_Format

val uLInformationTransferMRDC__criticalExtensions__c1__F1 :
  uLInformationTransferMRDC__criticalExtensions__c1__Type -> choice

val uLInformationTransferMRDC__criticalExtensions__c1__F2 :
  choice -> uLInformationTransferMRDC__criticalExtensions__c1__Type

val uLInformationTransferMRDC__criticalExtensions__c1__Format :
  uLInformationTransferMRDC__criticalExtensions__c1__Type t_Format

val uLInformationTransferMRDC__criticalExtensions__criticalExtensionsFuture__Format :
  uLInformationTransferMRDC__criticalExtensions__criticalExtensionsFuture__Type
  t_Format

val uLInformationTransferMRDC__criticalExtensions__list__Format :
  (int, __) sigT t_Format

val uLInformationTransferMRDC__criticalExtensions__F1 :
  uLInformationTransferMRDC__criticalExtensions__Type -> choice

val uLInformationTransferMRDC__criticalExtensions__F2 :
  choice -> uLInformationTransferMRDC__criticalExtensions__Type

val uLInformationTransferMRDC__criticalExtensions__Format :
  uLInformationTransferMRDC__criticalExtensions__Type t_Format

type uLInformationTransferMRDC__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val uLInformationTransferMRDC__Format_list :
  uLInformationTransferMRDC__Format_Type

val uLInformationTransferMRDC__list__Format : seq_type t_Format

val uLInformationTransferMRDC__F1 :
  uLInformationTransferMRDC__Type ->
  uLInformationTransferMRDC__criticalExtensions__Type * unit

val uLInformationTransferMRDC__F2 : seq_type -> uLInformationTransferMRDC__Type

val uLInformationTransferMRDC__Format :
  uLInformationTransferMRDC__Type t_Format

type measResultFreqList__Type = measResult2NR__Type list

val measResultFreqList__Format : measResultFreqList__Type t_Format

type perRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__Type =
| PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__true

val perRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__nat__Format :
  int t_Format

val perRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__F1 :
  perRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__Type -> int

val perRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__F2 :
  int -> perRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__Type

type perRAAttemptInfo_r16__ext0O__Type = { perRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17 : 
                                           perRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__Type
                                           option }

val perRAAttemptInfo_r16__ext0O__list : seq_elem list

type perRAAttemptInfo_r16__ext0__Type = perRAAttemptInfo_r16__ext0O__Type

type perRAAttemptInfo_r16__Type = { perRAAttemptInfo_r16__contentionDetected_r16 : 
                                    bool option;
                                    perRAAttemptInfo_r16__dlRSRPAboveThreshold_r16 : 
                                    bool option;
                                    perRAAttemptInfo_r16__ext0 : perRAAttemptInfo_r16__ext0__Type
                                                                 option }

val perRAAttemptInfo_r16__root_list : seq_elem list

val perRAAttemptInfo_r16__ext_list : typ list

val perRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__Format :
  perRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__Type t_Format

type perRAAttemptInfo_r16__ext0O__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val perRAAttemptInfo_r16__ext0O__Format_list :
  perRAAttemptInfo_r16__ext0O__Format_Type

val perRAAttemptInfo_r16__ext0O__list__Format : seq_type t_Format

val perRAAttemptInfo_r16__ext0O__F1 :
  perRAAttemptInfo_r16__ext0O__Type ->
  perRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__Type option * unit

val perRAAttemptInfo_r16__ext0O__F2 :
  seq_type -> perRAAttemptInfo_r16__ext0O__Type

val perRAAttemptInfo_r16__ext0O__Format :
  perRAAttemptInfo_r16__ext0O__Type t_Format

val perRAAttemptInfo_r16__ext0__check_all_none :
  perRAAttemptInfo_r16__ext0O__Type -> bool

val perRAAttemptInfo_r16__ext0__Format :
  perRAAttemptInfo_r16__ext0__Type t_Format

type perRAAttemptInfo_r16__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val perRAAttemptInfo_r16__root_Format_list :
  perRAAttemptInfo_r16__root_Format_Type

type perRAAttemptInfo_r16__ext_Format_Type =
  perRAAttemptInfo_r16__ext0__Type t_Format * unit t_Format

val perRAAttemptInfo_r16__ext_Format_list :
  perRAAttemptInfo_r16__ext_Format_Type

type perRAAttemptInfo_r16__list_type = seq_type * seq_ext_type

val perRAAttemptInfo_r16__list_format :
  perRAAttemptInfo_r16__list_type t_Format

val perRAAttemptInfo_r16__F1 :
  perRAAttemptInfo_r16__Type -> perRAAttemptInfo_r16__list_type

val perRAAttemptInfo_r16__F2 :
  perRAAttemptInfo_r16__list_type -> perRAAttemptInfo_r16__Type

val perRAAttemptInfo_r16__Format : perRAAttemptInfo_r16__Type t_Format

type perRAAttemptInfoList_r16__Type = perRAAttemptInfo_r16__Type list

val perRAAttemptInfoList_r16__Format : perRAAttemptInfoList_r16__Type t_Format

type perRASSBInfo_r16__Type = { perRASSBInfo_r16__ssb_Index_r16 : sSB_Index__Type;
                                perRASSBInfo_r16__numberOfPreamblesSentOnSSB_r16 : 
                                int;
                                perRASSBInfo_r16__perRAAttemptInfoList_r16 : 
                                perRAAttemptInfoList_r16__Type }

val perRASSBInfo_r16__list : seq_elem list

val perRASSBInfo_r16__numberOfPreamblesSentOnSSB_r16__Format : int t_Format

type perRASSBInfo_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val perRASSBInfo_r16__Format_list : perRASSBInfo_r16__Format_Type

val perRASSBInfo_r16__list__Format : seq_type t_Format

val perRASSBInfo_r16__F1 :
  perRASSBInfo_r16__Type ->
  sSB_Index__Type * (int * (perRAAttemptInfoList_r16__Type * unit))

val perRASSBInfo_r16__F2 : seq_type -> perRASSBInfo_r16__Type

val perRASSBInfo_r16__Format : perRASSBInfo_r16__Type t_Format

type perRACSI_RSInfo_r16__Type = { perRACSI_RSInfo_r16__csi_RS_Index_r16 : 
                                   cSI_RS_Index__Type;
                                   perRACSI_RSInfo_r16__numberOfPreamblesSentOnCSI_RS_r16 : 
                                   int }

val perRACSI_RSInfo_r16__list : seq_elem list

val perRACSI_RSInfo_r16__numberOfPreamblesSentOnCSI_RS_r16__Format :
  int t_Format

type perRACSI_RSInfo_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val perRACSI_RSInfo_r16__Format_list : perRACSI_RSInfo_r16__Format_Type

val perRACSI_RSInfo_r16__list__Format : seq_type t_Format

val perRACSI_RSInfo_r16__F1 :
  perRACSI_RSInfo_r16__Type -> cSI_RS_Index__Type * (int * unit)

val perRACSI_RSInfo_r16__F2 : seq_type -> perRACSI_RSInfo_r16__Type

val perRACSI_RSInfo_r16__Format : perRACSI_RSInfo_r16__Type t_Format

type perRAInfo_r16__Type =
| PerRAInfo_r16__perRASSBInfoList_r16 of perRASSBInfo_r16__Type
| PerRAInfo_r16__perRACSI_RSInfoList_r16 of perRACSI_RSInfo_r16__Type

val perRAInfo_r16__list__Format : (int, __) sigT t_Format

val perRAInfo_r16__F1 : perRAInfo_r16__Type -> choice

val perRAInfo_r16__F2 : choice -> perRAInfo_r16__Type

val perRAInfo_r16__Format : perRAInfo_r16__Type t_Format

type perRAInfoList_r16__Type = perRAInfo_r16__Type list

val perRAInfoList_r16__Format : perRAInfoList_r16__Type t_Format

type failureReportSCG__failureType__Type =
| FailureReportSCG__failureType__t310_Expiry
| FailureReportSCG__failureType__randomAccessProblem
| FailureReportSCG__failureType__rlc_MaxNumRetx
| FailureReportSCG__failureType__synchReconfigFailureSCG
| FailureReportSCG__failureType__scg_ReconfigFailure
| FailureReportSCG__failureType__srb3_IntegrityFailure
| FailureReportSCG__failureType__other_r16
| FailureReportSCG__failureType__spare1

val failureReportSCG__failureType__nat__Format : int t_Format

val failureReportSCG__failureType__F1 :
  failureReportSCG__failureType__Type -> int

val failureReportSCG__failureType__F2 :
  int -> failureReportSCG__failureType__Type

type failureReportSCG__ext0O__failureType_v1610__Type =
| FailureReportSCG__ext0O__failureType_v1610__scg_lbtFailure_r16
| FailureReportSCG__ext0O__failureType_v1610__beamFailureRecoveryFailure_r16
| FailureReportSCG__ext0O__failureType_v1610__t312_Expiry_r16
| FailureReportSCG__ext0O__failureType_v1610__bh_RLF_r16
| FailureReportSCG__ext0O__failureType_v1610__beamFailure_r17
| FailureReportSCG__ext0O__failureType_v1610__spare3
| FailureReportSCG__ext0O__failureType_v1610__spare2
| FailureReportSCG__ext0O__failureType_v1610__spare1

val failureReportSCG__ext0O__failureType_v1610__nat__Format : int t_Format

val failureReportSCG__ext0O__failureType_v1610__F1 :
  failureReportSCG__ext0O__failureType_v1610__Type -> int

val failureReportSCG__ext0O__failureType_v1610__F2 :
  int -> failureReportSCG__ext0O__failureType_v1610__Type

type failureReportSCG__ext0O__Type = { failureReportSCG__ext0O__locationInfo_r16 : 
                                       locationInfo_r16__Type option;
                                       failureReportSCG__ext0O__failureType_v1610 : 
                                       failureReportSCG__ext0O__failureType_v1610__Type
                                       option }

val failureReportSCG__ext0O__list : seq_elem list

type failureReportSCG__ext0__Type = failureReportSCG__ext0O__Type

type failureReportSCG__ext1O__previousPSCellId_r17__Type = { failureReportSCG__ext1O__previousPSCellId_r17__physCellId_r17 : 
                                                             physCellId__Type;
                                                             failureReportSCG__ext1O__previousPSCellId_r17__carrierFreq_r17 : 
                                                             aRFCN_ValueNR__Type }

val failureReportSCG__ext1O__previousPSCellId_r17__list : seq_elem list

type failureReportSCG__ext1O__failedPSCellId_r17__Type = { failureReportSCG__ext1O__failedPSCellId_r17__physCellId_r17 : 
                                                           physCellId__Type;
                                                           failureReportSCG__ext1O__failedPSCellId_r17__carrierFreq_r17 : 
                                                           aRFCN_ValueNR__Type }

val failureReportSCG__ext1O__failedPSCellId_r17__list : seq_elem list

type failureReportSCG__ext1O__Type = { failureReportSCG__ext1O__previousPSCellId_r17 : 
                                       failureReportSCG__ext1O__previousPSCellId_r17__Type
                                       option;
                                       failureReportSCG__ext1O__failedPSCellId_r17 : 
                                       failureReportSCG__ext1O__failedPSCellId_r17__Type
                                       option;
                                       failureReportSCG__ext1O__timeSCGFailure_r17 : 
                                       int option;
                                       failureReportSCG__ext1O__perRAInfoList_r17 : 
                                       perRAInfoList_r16__Type option }

val failureReportSCG__ext1O__list : seq_elem list

type failureReportSCG__ext1__Type = failureReportSCG__ext1O__Type

type failureReportSCG__Type = { failureReportSCG__failureType : failureReportSCG__failureType__Type;
                                failureReportSCG__measResultFreqList : 
                                measResultFreqList__Type option;
                                failureReportSCG__measResultSCG_Failure : 
                                octet_string option;
                                failureReportSCG__ext0 : failureReportSCG__ext0__Type
                                                         option;
                                failureReportSCG__ext1 : failureReportSCG__ext1__Type
                                                         option }

val failureReportSCG__root_list : seq_elem list

val failureReportSCG__ext_list : typ list

val failureReportSCG__failureType__Format :
  failureReportSCG__failureType__Type t_Format

val failureReportSCG__ext0O__failureType_v1610__Format :
  failureReportSCG__ext0O__failureType_v1610__Type t_Format

type failureReportSCG__ext0O__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val failureReportSCG__ext0O__Format_list : failureReportSCG__ext0O__Format_Type

val failureReportSCG__ext0O__list__Format : seq_type t_Format

val failureReportSCG__ext0O__F1 :
  failureReportSCG__ext0O__Type -> locationInfo_r16__Type
  option * (failureReportSCG__ext0O__failureType_v1610__Type option * unit)

val failureReportSCG__ext0O__F2 : seq_type -> failureReportSCG__ext0O__Type

val failureReportSCG__ext0O__Format : failureReportSCG__ext0O__Type t_Format

val failureReportSCG__ext0__check_all_none :
  failureReportSCG__ext0O__Type -> bool

val failureReportSCG__ext0__Format : failureReportSCG__ext0__Type t_Format

type failureReportSCG__ext1O__previousPSCellId_r17__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val failureReportSCG__ext1O__previousPSCellId_r17__Format_list :
  failureReportSCG__ext1O__previousPSCellId_r17__Format_Type

val failureReportSCG__ext1O__previousPSCellId_r17__list__Format :
  seq_type t_Format

val failureReportSCG__ext1O__previousPSCellId_r17__F1 :
  failureReportSCG__ext1O__previousPSCellId_r17__Type ->
  physCellId__Type * (aRFCN_ValueNR__Type * unit)

val failureReportSCG__ext1O__previousPSCellId_r17__F2 :
  seq_type -> failureReportSCG__ext1O__previousPSCellId_r17__Type

val failureReportSCG__ext1O__previousPSCellId_r17__Format :
  failureReportSCG__ext1O__previousPSCellId_r17__Type t_Format

type failureReportSCG__ext1O__failedPSCellId_r17__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val failureReportSCG__ext1O__failedPSCellId_r17__Format_list :
  failureReportSCG__ext1O__failedPSCellId_r17__Format_Type

val failureReportSCG__ext1O__failedPSCellId_r17__list__Format :
  seq_type t_Format

val failureReportSCG__ext1O__failedPSCellId_r17__F1 :
  failureReportSCG__ext1O__failedPSCellId_r17__Type ->
  physCellId__Type * (aRFCN_ValueNR__Type * unit)

val failureReportSCG__ext1O__failedPSCellId_r17__F2 :
  seq_type -> failureReportSCG__ext1O__failedPSCellId_r17__Type

val failureReportSCG__ext1O__failedPSCellId_r17__Format :
  failureReportSCG__ext1O__failedPSCellId_r17__Type t_Format

val failureReportSCG__ext1O__timeSCGFailure_r17__Format : int t_Format

type failureReportSCG__ext1O__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

val failureReportSCG__ext1O__Format_list : failureReportSCG__ext1O__Format_Type

val failureReportSCG__ext1O__list__Format : seq_type t_Format

val failureReportSCG__ext1O__F1 :
  failureReportSCG__ext1O__Type ->
  failureReportSCG__ext1O__previousPSCellId_r17__Type
  option * (failureReportSCG__ext1O__failedPSCellId_r17__Type option * (int
  option * (perRAInfoList_r16__Type option * unit)))

val failureReportSCG__ext1O__F2 : seq_type -> failureReportSCG__ext1O__Type

val failureReportSCG__ext1O__Format : failureReportSCG__ext1O__Type t_Format

val failureReportSCG__ext1__check_all_none :
  failureReportSCG__ext1O__Type -> bool

val failureReportSCG__ext1__Format : failureReportSCG__ext1__Type t_Format

type failureReportSCG__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val failureReportSCG__root_Format_list : failureReportSCG__root_Format_Type

type failureReportSCG__ext_Format_Type =
  failureReportSCG__ext0__Type t_Format * (failureReportSCG__ext1__Type
  t_Format * unit t_Format)

val failureReportSCG__ext_Format_list : failureReportSCG__ext_Format_Type

type failureReportSCG__list_type = seq_type * seq_ext_type

val failureReportSCG__list_format : failureReportSCG__list_type t_Format

val failureReportSCG__F1 :
  failureReportSCG__Type -> failureReportSCG__list_type

val failureReportSCG__F2 :
  failureReportSCG__list_type -> failureReportSCG__Type

val failureReportSCG__Format : failureReportSCG__Type t_Format

type sCGFailureInformation_v1590_IEs__nonCriticalExtension__Type =
| Make__SCGFailureInformation_v1590_IEs__nonCriticalExtension__Type

type sCGFailureInformation_v1590_IEs__Type = { sCGFailureInformation_v1590_IEs__lateNonCriticalExtension : 
                                               octet_string option;
                                               sCGFailureInformation_v1590_IEs__nonCriticalExtension : 
                                               sCGFailureInformation_v1590_IEs__nonCriticalExtension__Type
                                               option }

val sCGFailureInformation_v1590_IEs__list : seq_elem list

val sCGFailureInformation_v1590_IEs__nonCriticalExtension__Format :
  sCGFailureInformation_v1590_IEs__nonCriticalExtension__Type t_Format

type sCGFailureInformation_v1590_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val sCGFailureInformation_v1590_IEs__Format_list :
  sCGFailureInformation_v1590_IEs__Format_Type

val sCGFailureInformation_v1590_IEs__list__Format : seq_type t_Format

val sCGFailureInformation_v1590_IEs__F1 :
  sCGFailureInformation_v1590_IEs__Type -> octet_string
  option * (sCGFailureInformation_v1590_IEs__nonCriticalExtension__Type
  option * unit)

val sCGFailureInformation_v1590_IEs__F2 :
  seq_type -> sCGFailureInformation_v1590_IEs__Type

val sCGFailureInformation_v1590_IEs__Format :
  sCGFailureInformation_v1590_IEs__Type t_Format

type sCGFailureInformation_IEs__Type = { sCGFailureInformation_IEs__failureReportSCG : 
                                         failureReportSCG__Type option;
                                         sCGFailureInformation_IEs__nonCriticalExtension : 
                                         sCGFailureInformation_v1590_IEs__Type
                                         option }

val sCGFailureInformation_IEs__list : seq_elem list

type sCGFailureInformation_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val sCGFailureInformation_IEs__Format_list :
  sCGFailureInformation_IEs__Format_Type

val sCGFailureInformation_IEs__list__Format : seq_type t_Format

val sCGFailureInformation_IEs__F1 :
  sCGFailureInformation_IEs__Type -> failureReportSCG__Type
  option * (sCGFailureInformation_v1590_IEs__Type option * unit)

val sCGFailureInformation_IEs__F2 : seq_type -> sCGFailureInformation_IEs__Type

val sCGFailureInformation_IEs__Format :
  sCGFailureInformation_IEs__Type t_Format

type sCGFailureInformation__criticalExtensions__criticalExtensionsFuture__Type =
| Make__SCGFailureInformation__criticalExtensions__criticalExtensionsFuture__Type

type sCGFailureInformation__criticalExtensions__Type =
| SCGFailureInformation__criticalExtensions__scgFailureInformation of 
   sCGFailureInformation_IEs__Type
| SCGFailureInformation__criticalExtensions__criticalExtensionsFuture of 
   sCGFailureInformation__criticalExtensions__criticalExtensionsFuture__Type

type sCGFailureInformation__Type = { sCGFailureInformation__criticalExtensions : 
                                     sCGFailureInformation__criticalExtensions__Type }

val sCGFailureInformation__list : seq_elem list

val sCGFailureInformation__criticalExtensions__criticalExtensionsFuture__Format :
  sCGFailureInformation__criticalExtensions__criticalExtensionsFuture__Type
  t_Format

val sCGFailureInformation__criticalExtensions__list__Format :
  (int, __) sigT t_Format

val sCGFailureInformation__criticalExtensions__F1 :
  sCGFailureInformation__criticalExtensions__Type -> choice

val sCGFailureInformation__criticalExtensions__F2 :
  choice -> sCGFailureInformation__criticalExtensions__Type

val sCGFailureInformation__criticalExtensions__Format :
  sCGFailureInformation__criticalExtensions__Type t_Format

type sCGFailureInformation__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val sCGFailureInformation__Format_list : sCGFailureInformation__Format_Type

val sCGFailureInformation__list__Format : seq_type t_Format

val sCGFailureInformation__F1 :
  sCGFailureInformation__Type ->
  sCGFailureInformation__criticalExtensions__Type * unit

val sCGFailureInformation__F2 : seq_type -> sCGFailureInformation__Type

val sCGFailureInformation__Format : sCGFailureInformation__Type t_Format

type measResultFreqListFailMRDC__Type = measResult2EUTRA__Type list

val measResultFreqListFailMRDC__Format :
  measResultFreqListFailMRDC__Type t_Format

type failureReportSCG_EUTRA__failureType__Type =
| FailureReportSCG_EUTRA__failureType__t313_Expiry
| FailureReportSCG_EUTRA__failureType__randomAccessProblem
| FailureReportSCG_EUTRA__failureType__rlc_MaxNumRetx
| FailureReportSCG_EUTRA__failureType__scg_ChangeFailure
| FailureReportSCG_EUTRA__failureType__spare4
| FailureReportSCG_EUTRA__failureType__spare3
| FailureReportSCG_EUTRA__failureType__spare2
| FailureReportSCG_EUTRA__failureType__spare1

val failureReportSCG_EUTRA__failureType__nat__Format : int t_Format

val failureReportSCG_EUTRA__failureType__F1 :
  failureReportSCG_EUTRA__failureType__Type -> int

val failureReportSCG_EUTRA__failureType__F2 :
  int -> failureReportSCG_EUTRA__failureType__Type

type failureReportSCG_EUTRA__ext0O__Type = { failureReportSCG_EUTRA__ext0O__locationInfo_r16 : 
                                             locationInfo_r16__Type option }

val failureReportSCG_EUTRA__ext0O__list : seq_elem list

type failureReportSCG_EUTRA__ext0__Type = failureReportSCG_EUTRA__ext0O__Type

type failureReportSCG_EUTRA__Type = { failureReportSCG_EUTRA__failureType : 
                                      failureReportSCG_EUTRA__failureType__Type;
                                      failureReportSCG_EUTRA__measResultFreqListMRDC : 
                                      measResultFreqListFailMRDC__Type option;
                                      failureReportSCG_EUTRA__measResultSCG_FailureMRDC : 
                                      octet_string option;
                                      failureReportSCG_EUTRA__ext0 : failureReportSCG_EUTRA__ext0__Type
                                                                     option }

val failureReportSCG_EUTRA__root_list : seq_elem list

val failureReportSCG_EUTRA__ext_list : typ list

val failureReportSCG_EUTRA__failureType__Format :
  failureReportSCG_EUTRA__failureType__Type t_Format

type failureReportSCG_EUTRA__ext0O__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val failureReportSCG_EUTRA__ext0O__Format_list :
  failureReportSCG_EUTRA__ext0O__Format_Type

val failureReportSCG_EUTRA__ext0O__list__Format : seq_type t_Format

val failureReportSCG_EUTRA__ext0O__F1 :
  failureReportSCG_EUTRA__ext0O__Type -> locationInfo_r16__Type option * unit

val failureReportSCG_EUTRA__ext0O__F2 :
  seq_type -> failureReportSCG_EUTRA__ext0O__Type

val failureReportSCG_EUTRA__ext0O__Format :
  failureReportSCG_EUTRA__ext0O__Type t_Format

val failureReportSCG_EUTRA__ext0__check_all_none :
  failureReportSCG_EUTRA__ext0O__Type -> bool

val failureReportSCG_EUTRA__ext0__Format :
  failureReportSCG_EUTRA__ext0__Type t_Format

type failureReportSCG_EUTRA__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val failureReportSCG_EUTRA__root_Format_list :
  failureReportSCG_EUTRA__root_Format_Type

type failureReportSCG_EUTRA__ext_Format_Type =
  failureReportSCG_EUTRA__ext0__Type t_Format * unit t_Format

val failureReportSCG_EUTRA__ext_Format_list :
  failureReportSCG_EUTRA__ext_Format_Type

type failureReportSCG_EUTRA__list_type = seq_type * seq_ext_type

val failureReportSCG_EUTRA__list_format :
  failureReportSCG_EUTRA__list_type t_Format

val failureReportSCG_EUTRA__F1 :
  failureReportSCG_EUTRA__Type -> failureReportSCG_EUTRA__list_type

val failureReportSCG_EUTRA__F2 :
  failureReportSCG_EUTRA__list_type -> failureReportSCG_EUTRA__Type

val failureReportSCG_EUTRA__Format : failureReportSCG_EUTRA__Type t_Format

type sCGFailureInformationEUTRA_v1590_IEs__nonCriticalExtension__Type =
| Make__SCGFailureInformationEUTRA_v1590_IEs__nonCriticalExtension__Type

type sCGFailureInformationEUTRA_v1590_IEs__Type = { sCGFailureInformationEUTRA_v1590_IEs__lateNonCriticalExtension : 
                                                    octet_string option;
                                                    sCGFailureInformationEUTRA_v1590_IEs__nonCriticalExtension : 
                                                    sCGFailureInformationEUTRA_v1590_IEs__nonCriticalExtension__Type
                                                    option }

val sCGFailureInformationEUTRA_v1590_IEs__list : seq_elem list

val sCGFailureInformationEUTRA_v1590_IEs__nonCriticalExtension__Format :
  sCGFailureInformationEUTRA_v1590_IEs__nonCriticalExtension__Type t_Format

type sCGFailureInformationEUTRA_v1590_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val sCGFailureInformationEUTRA_v1590_IEs__Format_list :
  sCGFailureInformationEUTRA_v1590_IEs__Format_Type

val sCGFailureInformationEUTRA_v1590_IEs__list__Format : seq_type t_Format

val sCGFailureInformationEUTRA_v1590_IEs__F1 :
  sCGFailureInformationEUTRA_v1590_IEs__Type -> octet_string
  option * (sCGFailureInformationEUTRA_v1590_IEs__nonCriticalExtension__Type
  option * unit)

val sCGFailureInformationEUTRA_v1590_IEs__F2 :
  seq_type -> sCGFailureInformationEUTRA_v1590_IEs__Type

val sCGFailureInformationEUTRA_v1590_IEs__Format :
  sCGFailureInformationEUTRA_v1590_IEs__Type t_Format

type sCGFailureInformationEUTRA_IEs__Type = { sCGFailureInformationEUTRA_IEs__failureReportSCG_EUTRA : 
                                              failureReportSCG_EUTRA__Type
                                              option;
                                              sCGFailureInformationEUTRA_IEs__nonCriticalExtension : 
                                              sCGFailureInformationEUTRA_v1590_IEs__Type
                                              option }

val sCGFailureInformationEUTRA_IEs__list : seq_elem list

type sCGFailureInformationEUTRA_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val sCGFailureInformationEUTRA_IEs__Format_list :
  sCGFailureInformationEUTRA_IEs__Format_Type

val sCGFailureInformationEUTRA_IEs__list__Format : seq_type t_Format

val sCGFailureInformationEUTRA_IEs__F1 :
  sCGFailureInformationEUTRA_IEs__Type -> failureReportSCG_EUTRA__Type
  option * (sCGFailureInformationEUTRA_v1590_IEs__Type option * unit)

val sCGFailureInformationEUTRA_IEs__F2 :
  seq_type -> sCGFailureInformationEUTRA_IEs__Type

val sCGFailureInformationEUTRA_IEs__Format :
  sCGFailureInformationEUTRA_IEs__Type t_Format

type sCGFailureInformationEUTRA__criticalExtensions__criticalExtensionsFuture__Type =
| Make__SCGFailureInformationEUTRA__criticalExtensions__criticalExtensionsFuture__Type

type sCGFailureInformationEUTRA__criticalExtensions__Type =
| SCGFailureInformationEUTRA__criticalExtensions__scgFailureInformationEUTRA of 
   sCGFailureInformationEUTRA_IEs__Type
| SCGFailureInformationEUTRA__criticalExtensions__criticalExtensionsFuture of 
   sCGFailureInformationEUTRA__criticalExtensions__criticalExtensionsFuture__Type

type sCGFailureInformationEUTRA__Type = { sCGFailureInformationEUTRA__criticalExtensions : 
                                          sCGFailureInformationEUTRA__criticalExtensions__Type }

val sCGFailureInformationEUTRA__list : seq_elem list

val sCGFailureInformationEUTRA__criticalExtensions__criticalExtensionsFuture__Format :
  sCGFailureInformationEUTRA__criticalExtensions__criticalExtensionsFuture__Type
  t_Format

val sCGFailureInformationEUTRA__criticalExtensions__list__Format :
  (int, __) sigT t_Format

val sCGFailureInformationEUTRA__criticalExtensions__F1 :
  sCGFailureInformationEUTRA__criticalExtensions__Type -> choice

val sCGFailureInformationEUTRA__criticalExtensions__F2 :
  choice -> sCGFailureInformationEUTRA__criticalExtensions__Type

val sCGFailureInformationEUTRA__criticalExtensions__Format :
  sCGFailureInformationEUTRA__criticalExtensions__Type t_Format

type sCGFailureInformationEUTRA__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val sCGFailureInformationEUTRA__Format_list :
  sCGFailureInformationEUTRA__Format_Type

val sCGFailureInformationEUTRA__list__Format : seq_type t_Format

val sCGFailureInformationEUTRA__F1 :
  sCGFailureInformationEUTRA__Type ->
  sCGFailureInformationEUTRA__criticalExtensions__Type * unit

val sCGFailureInformationEUTRA__F2 :
  seq_type -> sCGFailureInformationEUTRA__Type

val sCGFailureInformationEUTRA__Format :
  sCGFailureInformationEUTRA__Type t_Format

type uLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__Type =
| ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__notLastSegment
| ULDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__lastSegment

val uLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__nat__Format :
  int t_Format

val uLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__F1 :
  uLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__Type -> int

val uLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__F2 :
  int -> uLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__Type

type uLDedicatedMessageSegment_r16_IEs__nonCriticalExtension__Type =
| Make__ULDedicatedMessageSegment_r16_IEs__nonCriticalExtension__Type

type uLDedicatedMessageSegment_r16_IEs__Type = { uLDedicatedMessageSegment_r16_IEs__segmentNumber_r16 : 
                                                 int;
                                                 uLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentContainer_r16 : 
                                                 octet_string;
                                                 uLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16 : 
                                                 uLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__Type;
                                                 uLDedicatedMessageSegment_r16_IEs__lateNonCriticalExtension : 
                                                 octet_string option;
                                                 uLDedicatedMessageSegment_r16_IEs__nonCriticalExtension : 
                                                 uLDedicatedMessageSegment_r16_IEs__nonCriticalExtension__Type
                                                 option }

val uLDedicatedMessageSegment_r16_IEs__list : seq_elem list

val uLDedicatedMessageSegment_r16_IEs__segmentNumber_r16__Format : int t_Format

val uLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__Format :
  uLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__Type t_Format

val uLDedicatedMessageSegment_r16_IEs__nonCriticalExtension__Format :
  uLDedicatedMessageSegment_r16_IEs__nonCriticalExtension__Type t_Format

type uLDedicatedMessageSegment_r16_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))))

val uLDedicatedMessageSegment_r16_IEs__Format_list :
  uLDedicatedMessageSegment_r16_IEs__Format_Type

val uLDedicatedMessageSegment_r16_IEs__list__Format : seq_type t_Format

val uLDedicatedMessageSegment_r16_IEs__F1 :
  uLDedicatedMessageSegment_r16_IEs__Type ->
  int * (octet_string * (uLDedicatedMessageSegment_r16_IEs__rrc_MessageSegmentType_r16__Type * (octet_string
  option * (uLDedicatedMessageSegment_r16_IEs__nonCriticalExtension__Type
  option * unit))))

val uLDedicatedMessageSegment_r16_IEs__F2 :
  seq_type -> uLDedicatedMessageSegment_r16_IEs__Type

val uLDedicatedMessageSegment_r16_IEs__Format :
  uLDedicatedMessageSegment_r16_IEs__Type t_Format

type uLDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__Type =
| Make__ULDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__Type

type uLDedicatedMessageSegment_r16__criticalExtensions__Type =
| ULDedicatedMessageSegment_r16__criticalExtensions__ulDedicatedMessageSegment_r16 of 
   uLDedicatedMessageSegment_r16_IEs__Type
| ULDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture of 
   uLDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__Type

type uLDedicatedMessageSegment_r16__Type = { uLDedicatedMessageSegment_r16__criticalExtensions : 
                                             uLDedicatedMessageSegment_r16__criticalExtensions__Type }

val uLDedicatedMessageSegment_r16__list : seq_elem list

val uLDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__Format :
  uLDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__Type
  t_Format

val uLDedicatedMessageSegment_r16__criticalExtensions__list__Format :
  (int, __) sigT t_Format

val uLDedicatedMessageSegment_r16__criticalExtensions__F1 :
  uLDedicatedMessageSegment_r16__criticalExtensions__Type -> choice

val uLDedicatedMessageSegment_r16__criticalExtensions__F2 :
  choice -> uLDedicatedMessageSegment_r16__criticalExtensions__Type

val uLDedicatedMessageSegment_r16__criticalExtensions__Format :
  uLDedicatedMessageSegment_r16__criticalExtensions__Type t_Format

type uLDedicatedMessageSegment_r16__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val uLDedicatedMessageSegment_r16__Format_list :
  uLDedicatedMessageSegment_r16__Format_Type

val uLDedicatedMessageSegment_r16__list__Format : seq_type t_Format

val uLDedicatedMessageSegment_r16__F1 :
  uLDedicatedMessageSegment_r16__Type ->
  uLDedicatedMessageSegment_r16__criticalExtensions__Type * unit

val uLDedicatedMessageSegment_r16__F2 :
  seq_type -> uLDedicatedMessageSegment_r16__Type

val uLDedicatedMessageSegment_r16__Format :
  uLDedicatedMessageSegment_r16__Type t_Format

type sIB_ReqInfo_r16__Type =
| SIB_ReqInfo_r16__sib12
| SIB_ReqInfo_r16__sib13
| SIB_ReqInfo_r16__sib14
| SIB_ReqInfo_r16__sib20_v1700
| SIB_ReqInfo_r16__sib21_v1700
| SIB_ReqInfo_r16__spare3
| SIB_ReqInfo_r16__spare2
| SIB_ReqInfo_r16__spare1

val sIB_ReqInfo_r16__nat__Format : int t_Format

val sIB_ReqInfo_r16__F1 : sIB_ReqInfo_r16__Type -> int

val sIB_ReqInfo_r16__F2 : int -> sIB_ReqInfo_r16__Type

val sIB_ReqInfo_r16__Format : sIB_ReqInfo_r16__Type t_Format

type gNSS_ID_r16__gnss_id_r16__root__Type =
| GNSS_ID_r16__gnss_id_r16__root__gps
| GNSS_ID_r16__gnss_id_r16__root__sbas
| GNSS_ID_r16__gnss_id_r16__root__qzss
| GNSS_ID_r16__gnss_id_r16__root__galileo
| GNSS_ID_r16__gnss_id_r16__root__glonass
| GNSS_ID_r16__gnss_id_r16__root__bds

val gNSS_ID_r16__gnss_id_r16__root__nat__Format : int t_Format

val gNSS_ID_r16__gnss_id_r16__root__F1 :
  gNSS_ID_r16__gnss_id_r16__root__Type -> int

val gNSS_ID_r16__gnss_id_r16__root__F2 :
  int -> gNSS_ID_r16__gnss_id_r16__root__Type

type gNSS_ID_r16__gnss_id_r16__ext__Type = empty_set

type gNSS_ID_r16__gnss_id_r16__Type =
  (gNSS_ID_r16__gnss_id_r16__root__Type, gNSS_ID_r16__gnss_id_r16__ext__Type)
  sum

type gNSS_ID_r16__Type = { gNSS_ID_r16__gnss_id_r16 : gNSS_ID_r16__gnss_id_r16__Type }

val gNSS_ID_r16__root_list : seq_elem list

val gNSS_ID_r16__ext_list : typ list

val gNSS_ID_r16__gnss_id_r16__root__Format :
  gNSS_ID_r16__gnss_id_r16__root__Type t_Format

val gNSS_ID_r16__gnss_id_r16__ext__Format :
  gNSS_ID_r16__gnss_id_r16__ext__Type t_Format

val gNSS_ID_r16__gnss_id_r16__Format : gNSS_ID_r16__gnss_id_r16__Type t_Format

type gNSS_ID_r16__root_Format_Type = seq_elem_to_format * seq_elem_to_format

val gNSS_ID_r16__root_Format_list : gNSS_ID_r16__root_Format_Type

type gNSS_ID_r16__ext_Format_Type = unit t_Format

val gNSS_ID_r16__ext_Format_list : gNSS_ID_r16__ext_Format_Type

type gNSS_ID_r16__list_type = seq_type * seq_ext_type

val gNSS_ID_r16__list_format : gNSS_ID_r16__list_type t_Format

val gNSS_ID_r16__F1 : gNSS_ID_r16__Type -> gNSS_ID_r16__list_type

val gNSS_ID_r16__F2 : gNSS_ID_r16__list_type -> gNSS_ID_r16__Type

val gNSS_ID_r16__Format : gNSS_ID_r16__Type t_Format

type sBAS_ID_r16__sbas_id_r16__root__Type =
| SBAS_ID_r16__sbas_id_r16__root__waas
| SBAS_ID_r16__sbas_id_r16__root__egnos
| SBAS_ID_r16__sbas_id_r16__root__msas
| SBAS_ID_r16__sbas_id_r16__root__gagan

val sBAS_ID_r16__sbas_id_r16__root__nat__Format : int t_Format

val sBAS_ID_r16__sbas_id_r16__root__F1 :
  sBAS_ID_r16__sbas_id_r16__root__Type -> int

val sBAS_ID_r16__sbas_id_r16__root__F2 :
  int -> sBAS_ID_r16__sbas_id_r16__root__Type

type sBAS_ID_r16__sbas_id_r16__ext__Type = empty_set

type sBAS_ID_r16__sbas_id_r16__Type =
  (sBAS_ID_r16__sbas_id_r16__root__Type, sBAS_ID_r16__sbas_id_r16__ext__Type)
  sum

type sBAS_ID_r16__Type = { sBAS_ID_r16__sbas_id_r16 : sBAS_ID_r16__sbas_id_r16__Type }

val sBAS_ID_r16__root_list : seq_elem list

val sBAS_ID_r16__ext_list : typ list

val sBAS_ID_r16__sbas_id_r16__root__Format :
  sBAS_ID_r16__sbas_id_r16__root__Type t_Format

val sBAS_ID_r16__sbas_id_r16__ext__Format :
  sBAS_ID_r16__sbas_id_r16__ext__Type t_Format

val sBAS_ID_r16__sbas_id_r16__Format : sBAS_ID_r16__sbas_id_r16__Type t_Format

type sBAS_ID_r16__root_Format_Type = seq_elem_to_format * seq_elem_to_format

val sBAS_ID_r16__root_Format_list : sBAS_ID_r16__root_Format_Type

type sBAS_ID_r16__ext_Format_Type = unit t_Format

val sBAS_ID_r16__ext_Format_list : sBAS_ID_r16__ext_Format_Type

type sBAS_ID_r16__list_type = seq_type * seq_ext_type

val sBAS_ID_r16__list_format : sBAS_ID_r16__list_type t_Format

val sBAS_ID_r16__F1 : sBAS_ID_r16__Type -> sBAS_ID_r16__list_type

val sBAS_ID_r16__F2 : sBAS_ID_r16__list_type -> sBAS_ID_r16__Type

val sBAS_ID_r16__Format : sBAS_ID_r16__Type t_Format

type posSIB_ReqInfo_r16__posSibType_r16__root__Type =
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType1_1
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType1_2
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType1_3
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType1_4
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType1_5
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType1_6
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType1_7
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType1_8
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType2_1
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType2_2
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType2_3
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType2_4
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType2_5
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType2_6
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType2_7
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType2_8
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType2_9
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType2_10
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType2_11
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType2_12
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType2_13
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType2_14
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType2_15
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType2_16
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType2_17
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType2_18
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType2_19
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType2_20
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType2_21
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType2_22
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType2_23
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType3_1
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType4_1
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType5_1
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType6_1
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType6_2
| PosSIB_ReqInfo_r16__posSibType_r16__root__posSibType6_3

val posSIB_ReqInfo_r16__posSibType_r16__root__nat__Format : int t_Format

val posSIB_ReqInfo_r16__posSibType_r16__root__F1 :
  posSIB_ReqInfo_r16__posSibType_r16__root__Type -> int

val posSIB_ReqInfo_r16__posSibType_r16__root__F2 :
  int -> posSIB_ReqInfo_r16__posSibType_r16__root__Type

type posSIB_ReqInfo_r16__posSibType_r16__ext__Type =
| PosSIB_ReqInfo_r16__posSibType_r16__ext__posSibType1_9_v1710
| PosSIB_ReqInfo_r16__posSibType_r16__ext__posSibType1_10_v1710
| PosSIB_ReqInfo_r16__posSibType_r16__ext__posSibType2_24_v1710
| PosSIB_ReqInfo_r16__posSibType_r16__ext__posSibType2_25_v1710
| PosSIB_ReqInfo_r16__posSibType_r16__ext__posSibType6_4_v1710
| PosSIB_ReqInfo_r16__posSibType_r16__ext__posSibType6_5_v1710
| PosSIB_ReqInfo_r16__posSibType_r16__ext__posSibType6_6_v1710

val posSIB_ReqInfo_r16__posSibType_r16__ext__F1 :
  posSIB_ReqInfo_r16__posSibType_r16__ext__Type -> int

val posSIB_ReqInfo_r16__posSibType_r16__ext__F2 :
  int -> posSIB_ReqInfo_r16__posSibType_r16__ext__Type

val posSIB_ReqInfo_r16__posSibType_r16__ext__helper_format : int t_Format

type posSIB_ReqInfo_r16__posSibType_r16__Type =
  (posSIB_ReqInfo_r16__posSibType_r16__root__Type,
  posSIB_ReqInfo_r16__posSibType_r16__ext__Type) sum

type posSIB_ReqInfo_r16__Type = { posSIB_ReqInfo_r16__gnss_id_r16 : gNSS_ID_r16__Type
                                                                    option;
                                  posSIB_ReqInfo_r16__sbas_id_r16 : sBAS_ID_r16__Type
                                                                    option;
                                  posSIB_ReqInfo_r16__posSibType_r16 : 
                                  posSIB_ReqInfo_r16__posSibType_r16__Type }

val posSIB_ReqInfo_r16__list : seq_elem list

val posSIB_ReqInfo_r16__posSibType_r16__root__Format :
  posSIB_ReqInfo_r16__posSibType_r16__root__Type t_Format

val posSIB_ReqInfo_r16__posSibType_r16__ext__Format :
  posSIB_ReqInfo_r16__posSibType_r16__ext__Type t_Format

val posSIB_ReqInfo_r16__posSibType_r16__Format :
  posSIB_ReqInfo_r16__posSibType_r16__Type t_Format

type posSIB_ReqInfo_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val posSIB_ReqInfo_r16__Format_list : posSIB_ReqInfo_r16__Format_Type

val posSIB_ReqInfo_r16__list__Format : seq_type t_Format

val posSIB_ReqInfo_r16__F1 :
  posSIB_ReqInfo_r16__Type -> gNSS_ID_r16__Type option * (sBAS_ID_r16__Type
  option * (posSIB_ReqInfo_r16__posSibType_r16__Type * unit))

val posSIB_ReqInfo_r16__F2 : seq_type -> posSIB_ReqInfo_r16__Type

val posSIB_ReqInfo_r16__Format : posSIB_ReqInfo_r16__Type t_Format

type dedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedSIB_List_r16__Type =
  sIB_ReqInfo_r16__Type list

type dedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedPosSIB_List_r16__Type =
  posSIB_ReqInfo_r16__Type list

type dedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__Type = { 
dedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedSIB_List_r16 : 
dedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedSIB_List_r16__Type
option;
dedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedPosSIB_List_r16 : 
dedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedPosSIB_List_r16__Type
option }

val dedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__list :
  seq_elem list

type dedicatedSIBRequest_r16_IEs__nonCriticalExtension__Type =
| Make__DedicatedSIBRequest_r16_IEs__nonCriticalExtension__Type

type dedicatedSIBRequest_r16_IEs__Type = { dedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16 : 
                                           dedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__Type
                                           option;
                                           dedicatedSIBRequest_r16_IEs__lateNonCriticalExtension : 
                                           octet_string option;
                                           dedicatedSIBRequest_r16_IEs__nonCriticalExtension : 
                                           dedicatedSIBRequest_r16_IEs__nonCriticalExtension__Type
                                           option }

val dedicatedSIBRequest_r16_IEs__list : seq_elem list

val dedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedSIB_List_r16__Format :
  dedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedSIB_List_r16__Type
  t_Format

val dedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedPosSIB_List_r16__Format :
  dedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedPosSIB_List_r16__Type
  t_Format

type dedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val dedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__Format_list :
  dedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__Format_Type

val dedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__list__Format :
  seq_type t_Format

val dedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__F1 :
  dedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__Type ->
  dedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedSIB_List_r16__Type
  option * (dedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedPosSIB_List_r16__Type
  option * unit)

val dedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__F2 :
  seq_type -> dedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__Type

val dedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__Format :
  dedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__Type t_Format

val dedicatedSIBRequest_r16_IEs__nonCriticalExtension__Format :
  dedicatedSIBRequest_r16_IEs__nonCriticalExtension__Type t_Format

type dedicatedSIBRequest_r16_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val dedicatedSIBRequest_r16_IEs__Format_list :
  dedicatedSIBRequest_r16_IEs__Format_Type

val dedicatedSIBRequest_r16_IEs__list__Format : seq_type t_Format

val dedicatedSIBRequest_r16_IEs__F1 :
  dedicatedSIBRequest_r16_IEs__Type ->
  dedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__Type
  option * (octet_string
  option * (dedicatedSIBRequest_r16_IEs__nonCriticalExtension__Type
  option * unit))

val dedicatedSIBRequest_r16_IEs__F2 :
  seq_type -> dedicatedSIBRequest_r16_IEs__Type

val dedicatedSIBRequest_r16_IEs__Format :
  dedicatedSIBRequest_r16_IEs__Type t_Format

type dedicatedSIBRequest_r16__criticalExtensions__criticalExtensionsFuture__Type =
| Make__DedicatedSIBRequest_r16__criticalExtensions__criticalExtensionsFuture__Type

type dedicatedSIBRequest_r16__criticalExtensions__Type =
| DedicatedSIBRequest_r16__criticalExtensions__dedicatedSIBRequest_r16 of 
   dedicatedSIBRequest_r16_IEs__Type
| DedicatedSIBRequest_r16__criticalExtensions__criticalExtensionsFuture of 
   dedicatedSIBRequest_r16__criticalExtensions__criticalExtensionsFuture__Type

type dedicatedSIBRequest_r16__Type = { dedicatedSIBRequest_r16__criticalExtensions : 
                                       dedicatedSIBRequest_r16__criticalExtensions__Type }

val dedicatedSIBRequest_r16__list : seq_elem list

val dedicatedSIBRequest_r16__criticalExtensions__criticalExtensionsFuture__Format :
  dedicatedSIBRequest_r16__criticalExtensions__criticalExtensionsFuture__Type
  t_Format

val dedicatedSIBRequest_r16__criticalExtensions__list__Format :
  (int, __) sigT t_Format

val dedicatedSIBRequest_r16__criticalExtensions__F1 :
  dedicatedSIBRequest_r16__criticalExtensions__Type -> choice

val dedicatedSIBRequest_r16__criticalExtensions__F2 :
  choice -> dedicatedSIBRequest_r16__criticalExtensions__Type

val dedicatedSIBRequest_r16__criticalExtensions__Format :
  dedicatedSIBRequest_r16__criticalExtensions__Type t_Format

type dedicatedSIBRequest_r16__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val dedicatedSIBRequest_r16__Format_list : dedicatedSIBRequest_r16__Format_Type

val dedicatedSIBRequest_r16__list__Format : seq_type t_Format

val dedicatedSIBRequest_r16__F1 :
  dedicatedSIBRequest_r16__Type ->
  dedicatedSIBRequest_r16__criticalExtensions__Type * unit

val dedicatedSIBRequest_r16__F2 : seq_type -> dedicatedSIBRequest_r16__Type

val dedicatedSIBRequest_r16__Format : dedicatedSIBRequest_r16__Type t_Format

type measResultList2NR__Type = measResult2NR__Type list

val measResultList2NR__Format : measResultList2NR__Type t_Format

type measResult2EUTRA_r16__Type = { measResult2EUTRA_r16__carrierFreq_r16 : 
                                    aRFCN_ValueEUTRA__Type;
                                    measResult2EUTRA_r16__measResultList_r16 : 
                                    measResultListEUTRA__Type }

val measResult2EUTRA_r16__list : seq_elem list

type measResult2EUTRA_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val measResult2EUTRA_r16__Format_list : measResult2EUTRA_r16__Format_Type

val measResult2EUTRA_r16__list__Format : seq_type t_Format

val measResult2EUTRA_r16__F1 :
  measResult2EUTRA_r16__Type ->
  aRFCN_ValueEUTRA__Type * (measResultListEUTRA__Type * unit)

val measResult2EUTRA_r16__F2 : seq_type -> measResult2EUTRA_r16__Type

val measResult2EUTRA_r16__Format : measResult2EUTRA_r16__Type t_Format

type measResultList2EUTRA__Type = measResult2EUTRA_r16__Type list

val measResultList2EUTRA__Format : measResultList2EUTRA__Type t_Format

type aRFCN_ValueUTRA_FDD_r16__Type = int

val aRFCN_ValueUTRA_FDD_r16__Format : int t_Format

type measResult2UTRA_FDD_r16__Type = { measResult2UTRA_FDD_r16__carrierFreq_r16 : 
                                       aRFCN_ValueUTRA_FDD_r16__Type;
                                       measResult2UTRA_FDD_r16__measResultNeighCellList_r16 : 
                                       measResultListUTRA_FDD_r16__Type }

val measResult2UTRA_FDD_r16__list : seq_elem list

type measResult2UTRA_FDD_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val measResult2UTRA_FDD_r16__Format_list : measResult2UTRA_FDD_r16__Format_Type

val measResult2UTRA_FDD_r16__list__Format : seq_type t_Format

val measResult2UTRA_FDD_r16__F1 :
  measResult2UTRA_FDD_r16__Type ->
  aRFCN_ValueUTRA_FDD_r16__Type * (measResultListUTRA_FDD_r16__Type * unit)

val measResult2UTRA_FDD_r16__F2 : seq_type -> measResult2UTRA_FDD_r16__Type

val measResult2UTRA_FDD_r16__Format : measResult2UTRA_FDD_r16__Type t_Format

type measResultList2UTRA__Type = measResult2UTRA_FDD_r16__Type list

val measResultList2UTRA__Format : measResultList2UTRA__Type t_Format

type failureReportMCG_r16__failureType_r16__Type =
| FailureReportMCG_r16__failureType_r16__t310_Expiry
| FailureReportMCG_r16__failureType_r16__randomAccessProblem
| FailureReportMCG_r16__failureType_r16__rlc_MaxNumRetx
| FailureReportMCG_r16__failureType_r16__t312_Expiry_r16
| FailureReportMCG_r16__failureType_r16__lbt_Failure_r16
| FailureReportMCG_r16__failureType_r16__beamFailureRecoveryFailure_r16
| FailureReportMCG_r16__failureType_r16__bh_RLF_r16
| FailureReportMCG_r16__failureType_r16__spare1

val failureReportMCG_r16__failureType_r16__nat__Format : int t_Format

val failureReportMCG_r16__failureType_r16__F1 :
  failureReportMCG_r16__failureType_r16__Type -> int

val failureReportMCG_r16__failureType_r16__F2 :
  int -> failureReportMCG_r16__failureType_r16__Type

type failureReportMCG_r16__Type = { failureReportMCG_r16__failureType_r16 : 
                                    failureReportMCG_r16__failureType_r16__Type
                                    option;
                                    failureReportMCG_r16__measResultFreqList_r16 : 
                                    measResultList2NR__Type option;
                                    failureReportMCG_r16__measResultFreqListEUTRA_r16 : 
                                    measResultList2EUTRA__Type option;
                                    failureReportMCG_r16__measResultSCG_r16 : 
                                    octet_string option;
                                    failureReportMCG_r16__measResultSCG_EUTRA_r16 : 
                                    octet_string option;
                                    failureReportMCG_r16__measResultFreqListUTRA_FDD_r16 : 
                                    measResultList2UTRA__Type option }

val failureReportMCG_r16__root_list : seq_elem list

val failureReportMCG_r16__ext_list : typ list

val failureReportMCG_r16__failureType_r16__Format :
  failureReportMCG_r16__failureType_r16__Type t_Format

type failureReportMCG_r16__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))))

val failureReportMCG_r16__root_Format_list :
  failureReportMCG_r16__root_Format_Type

type failureReportMCG_r16__ext_Format_Type = unit t_Format

val failureReportMCG_r16__ext_Format_list :
  failureReportMCG_r16__ext_Format_Type

type failureReportMCG_r16__list_type = seq_type * seq_ext_type

val failureReportMCG_r16__list_format :
  failureReportMCG_r16__list_type t_Format

val failureReportMCG_r16__F1 :
  failureReportMCG_r16__Type -> failureReportMCG_r16__list_type

val failureReportMCG_r16__F2 :
  failureReportMCG_r16__list_type -> failureReportMCG_r16__Type

val failureReportMCG_r16__Format : failureReportMCG_r16__Type t_Format

type mCGFailureInformation_r16_IEs__nonCriticalExtension__Type =
| Make__MCGFailureInformation_r16_IEs__nonCriticalExtension__Type

type mCGFailureInformation_r16_IEs__Type = { mCGFailureInformation_r16_IEs__failureReportMCG_r16 : 
                                             failureReportMCG_r16__Type option;
                                             mCGFailureInformation_r16_IEs__lateNonCriticalExtension : 
                                             octet_string option;
                                             mCGFailureInformation_r16_IEs__nonCriticalExtension : 
                                             mCGFailureInformation_r16_IEs__nonCriticalExtension__Type
                                             option }

val mCGFailureInformation_r16_IEs__list : seq_elem list

val mCGFailureInformation_r16_IEs__nonCriticalExtension__Format :
  mCGFailureInformation_r16_IEs__nonCriticalExtension__Type t_Format

type mCGFailureInformation_r16_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val mCGFailureInformation_r16_IEs__Format_list :
  mCGFailureInformation_r16_IEs__Format_Type

val mCGFailureInformation_r16_IEs__list__Format : seq_type t_Format

val mCGFailureInformation_r16_IEs__F1 :
  mCGFailureInformation_r16_IEs__Type -> failureReportMCG_r16__Type
  option * (octet_string
  option * (mCGFailureInformation_r16_IEs__nonCriticalExtension__Type
  option * unit))

val mCGFailureInformation_r16_IEs__F2 :
  seq_type -> mCGFailureInformation_r16_IEs__Type

val mCGFailureInformation_r16_IEs__Format :
  mCGFailureInformation_r16_IEs__Type t_Format

type mCGFailureInformation_r16__criticalExtensions__criticalExtensionsFuture__Type =
| Make__MCGFailureInformation_r16__criticalExtensions__criticalExtensionsFuture__Type

type mCGFailureInformation_r16__criticalExtensions__Type =
| MCGFailureInformation_r16__criticalExtensions__mcgFailureInformation_r16 of 
   mCGFailureInformation_r16_IEs__Type
| MCGFailureInformation_r16__criticalExtensions__criticalExtensionsFuture of 
   mCGFailureInformation_r16__criticalExtensions__criticalExtensionsFuture__Type

type mCGFailureInformation_r16__Type = { mCGFailureInformation_r16__criticalExtensions : 
                                         mCGFailureInformation_r16__criticalExtensions__Type }

val mCGFailureInformation_r16__list : seq_elem list

val mCGFailureInformation_r16__criticalExtensions__criticalExtensionsFuture__Format :
  mCGFailureInformation_r16__criticalExtensions__criticalExtensionsFuture__Type
  t_Format

val mCGFailureInformation_r16__criticalExtensions__list__Format :
  (int, __) sigT t_Format

val mCGFailureInformation_r16__criticalExtensions__F1 :
  mCGFailureInformation_r16__criticalExtensions__Type -> choice

val mCGFailureInformation_r16__criticalExtensions__F2 :
  choice -> mCGFailureInformation_r16__criticalExtensions__Type

val mCGFailureInformation_r16__criticalExtensions__Format :
  mCGFailureInformation_r16__criticalExtensions__Type t_Format

type mCGFailureInformation_r16__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val mCGFailureInformation_r16__Format_list :
  mCGFailureInformation_r16__Format_Type

val mCGFailureInformation_r16__list__Format : seq_type t_Format

val mCGFailureInformation_r16__F1 :
  mCGFailureInformation_r16__Type ->
  mCGFailureInformation_r16__criticalExtensions__Type * unit

val mCGFailureInformation_r16__F2 : seq_type -> mCGFailureInformation_r16__Type

val mCGFailureInformation_r16__Format :
  mCGFailureInformation_r16__Type t_Format

type absoluteTimeInfo_r16__Type = bit_string_fixed

val absoluteTimeInfo_r16__Format : absoluteTimeInfo_r16__Type t_Format

type traceReference_r16__traceId_r16__Type = octet_string

type traceReference_r16__Type = { traceReference_r16__plmn_Identity_r16 : 
                                  pLMN_Identity__Type;
                                  traceReference_r16__traceId_r16 : traceReference_r16__traceId_r16__Type }

val traceReference_r16__list : seq_elem list

val traceReference_r16__traceId_r16__Format :
  traceReference_r16__traceId_r16__Type t_Format

type traceReference_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val traceReference_r16__Format_list : traceReference_r16__Format_Type

val traceReference_r16__list__Format : seq_type t_Format

val traceReference_r16__F1 :
  traceReference_r16__Type ->
  pLMN_Identity__Type * (traceReference_r16__traceId_r16__Type * unit)

val traceReference_r16__F2 : seq_type -> traceReference_r16__Type

val traceReference_r16__Format : traceReference_r16__Type t_Format

type cGI_Info_Logging_r16__Type = { cGI_Info_Logging_r16__plmn_Identity_r16 : 
                                    pLMN_Identity__Type;
                                    cGI_Info_Logging_r16__cellIdentity_r16 : 
                                    cellIdentity__Type;
                                    cGI_Info_Logging_r16__trackingAreaCode_r16 : 
                                    trackingAreaCode__Type option }

val cGI_Info_Logging_r16__list : seq_elem list

type cGI_Info_Logging_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val cGI_Info_Logging_r16__Format_list : cGI_Info_Logging_r16__Format_Type

val cGI_Info_Logging_r16__list__Format : seq_type t_Format

val cGI_Info_Logging_r16__F1 :
  cGI_Info_Logging_r16__Type ->
  pLMN_Identity__Type * (cellIdentity__Type * (trackingAreaCode__Type
  option * unit))

val cGI_Info_Logging_r16__F2 : seq_type -> cGI_Info_Logging_r16__Type

val cGI_Info_Logging_r16__Format : cGI_Info_Logging_r16__Type t_Format

type measResultServingCell_r16__resultsSSB__Type = { measResultServingCell_r16__resultsSSB__best_ssb_Index : 
                                                     sSB_Index__Type;
                                                     measResultServingCell_r16__resultsSSB__best_ssb_Results : 
                                                     measQuantityResults__Type;
                                                     measResultServingCell_r16__resultsSSB__numberOfGoodSSB : 
                                                     int }

val measResultServingCell_r16__resultsSSB__list : seq_elem list

type measResultServingCell_r16__Type = { measResultServingCell_r16__resultsSSB_Cell : 
                                         measQuantityResults__Type;
                                         measResultServingCell_r16__resultsSSB : 
                                         measResultServingCell_r16__resultsSSB__Type
                                         option }

val measResultServingCell_r16__list : seq_elem list

val measResultServingCell_r16__resultsSSB__numberOfGoodSSB__Format :
  int t_Format

type measResultServingCell_r16__resultsSSB__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val measResultServingCell_r16__resultsSSB__Format_list :
  measResultServingCell_r16__resultsSSB__Format_Type

val measResultServingCell_r16__resultsSSB__list__Format : seq_type t_Format

val measResultServingCell_r16__resultsSSB__F1 :
  measResultServingCell_r16__resultsSSB__Type ->
  sSB_Index__Type * (measQuantityResults__Type * (int * unit))

val measResultServingCell_r16__resultsSSB__F2 :
  seq_type -> measResultServingCell_r16__resultsSSB__Type

val measResultServingCell_r16__resultsSSB__Format :
  measResultServingCell_r16__resultsSSB__Type t_Format

type measResultServingCell_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val measResultServingCell_r16__Format_list :
  measResultServingCell_r16__Format_Type

val measResultServingCell_r16__list__Format : seq_type t_Format

val measResultServingCell_r16__F1 :
  measResultServingCell_r16__Type ->
  measQuantityResults__Type * (measResultServingCell_r16__resultsSSB__Type
  option * unit)

val measResultServingCell_r16__F2 : seq_type -> measResultServingCell_r16__Type

val measResultServingCell_r16__Format :
  measResultServingCell_r16__Type t_Format

type measResultLoggingNR_r16__Type = { measResultLoggingNR_r16__physCellId_r16 : 
                                       physCellId__Type;
                                       measResultLoggingNR_r16__resultsSSB_Cell_r16 : 
                                       measQuantityResults__Type;
                                       measResultLoggingNR_r16__numberOfGoodSSB_r16 : 
                                       int option }

val measResultLoggingNR_r16__list : seq_elem list

val measResultLoggingNR_r16__numberOfGoodSSB_r16__Format : int t_Format

type measResultLoggingNR_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val measResultLoggingNR_r16__Format_list : measResultLoggingNR_r16__Format_Type

val measResultLoggingNR_r16__list__Format : seq_type t_Format

val measResultLoggingNR_r16__F1 :
  measResultLoggingNR_r16__Type ->
  physCellId__Type * (measQuantityResults__Type * (int option * unit))

val measResultLoggingNR_r16__F2 : seq_type -> measResultLoggingNR_r16__Type

val measResultLoggingNR_r16__Format : measResultLoggingNR_r16__Type t_Format

type measResultListLoggingNR_r16__Type = measResultLoggingNR_r16__Type list

val measResultListLoggingNR_r16__Format :
  measResultListLoggingNR_r16__Type t_Format

type measResultLogging2NR_r16__Type = { measResultLogging2NR_r16__carrierFreq_r16 : 
                                        aRFCN_ValueNR__Type;
                                        measResultLogging2NR_r16__measResultListLoggingNR_r16 : 
                                        measResultListLoggingNR_r16__Type }

val measResultLogging2NR_r16__list : seq_elem list

type measResultLogging2NR_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val measResultLogging2NR_r16__Format_list :
  measResultLogging2NR_r16__Format_Type

val measResultLogging2NR_r16__list__Format : seq_type t_Format

val measResultLogging2NR_r16__F1 :
  measResultLogging2NR_r16__Type ->
  aRFCN_ValueNR__Type * (measResultListLoggingNR_r16__Type * unit)

val measResultLogging2NR_r16__F2 : seq_type -> measResultLogging2NR_r16__Type

val measResultLogging2NR_r16__Format : measResultLogging2NR_r16__Type t_Format

type measResultListLogging2NR_r16__Type = measResultLogging2NR_r16__Type list

val measResultListLogging2NR_r16__Format :
  measResultListLogging2NR_r16__Type t_Format

type measResultList2EUTRA_r16__Type = measResult2EUTRA_r16__Type list

val measResultList2EUTRA_r16__Format : measResultList2EUTRA_r16__Type t_Format

type logMeasInfo_r16__measResultNeighCells_r16__Type = { logMeasInfo_r16__measResultNeighCells_r16__measResultNeighCellListNR : 
                                                         measResultListLogging2NR_r16__Type
                                                         option;
                                                         logMeasInfo_r16__measResultNeighCells_r16__measResultNeighCellListEUTRA : 
                                                         measResultList2EUTRA_r16__Type
                                                         option }

val logMeasInfo_r16__measResultNeighCells_r16__list : seq_elem list

type logMeasInfo_r16__anyCellSelectionDetected_r16__Type =
| LogMeasInfo_r16__anyCellSelectionDetected_r16__true

val logMeasInfo_r16__anyCellSelectionDetected_r16__nat__Format : int t_Format

val logMeasInfo_r16__anyCellSelectionDetected_r16__F1 :
  logMeasInfo_r16__anyCellSelectionDetected_r16__Type -> int

val logMeasInfo_r16__anyCellSelectionDetected_r16__F2 :
  int -> logMeasInfo_r16__anyCellSelectionDetected_r16__Type

type logMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__Type =
| LogMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__true

val logMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__nat__Format :
  int t_Format

val logMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__F1 :
  logMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__Type -> int

val logMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__F2 :
  int -> logMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__Type

type logMeasInfo_r16__ext0O__Type = { logMeasInfo_r16__ext0O__inDeviceCoexDetected_r17 : 
                                      logMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__Type
                                      option }

val logMeasInfo_r16__ext0O__list : seq_elem list

type logMeasInfo_r16__ext0__Type = logMeasInfo_r16__ext0O__Type

type logMeasInfo_r16__Type = { logMeasInfo_r16__locationInfo_r16 : locationInfo_r16__Type
                                                                   option;
                               logMeasInfo_r16__relativeTimeStamp_r16 : 
                               int;
                               logMeasInfo_r16__servCellIdentity_r16 : 
                               cGI_Info_Logging_r16__Type option;
                               logMeasInfo_r16__measResultServingCell_r16 : 
                               measResultServingCell_r16__Type option;
                               logMeasInfo_r16__measResultNeighCells_r16 : 
                               logMeasInfo_r16__measResultNeighCells_r16__Type;
                               logMeasInfo_r16__anyCellSelectionDetected_r16 : 
                               logMeasInfo_r16__anyCellSelectionDetected_r16__Type
                               option;
                               logMeasInfo_r16__ext0 : logMeasInfo_r16__ext0__Type
                                                       option }

val logMeasInfo_r16__root_list : seq_elem list

val logMeasInfo_r16__ext_list : typ list

val logMeasInfo_r16__relativeTimeStamp_r16__Format : int t_Format

type logMeasInfo_r16__measResultNeighCells_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val logMeasInfo_r16__measResultNeighCells_r16__Format_list :
  logMeasInfo_r16__measResultNeighCells_r16__Format_Type

val logMeasInfo_r16__measResultNeighCells_r16__list__Format : seq_type t_Format

val logMeasInfo_r16__measResultNeighCells_r16__F1 :
  logMeasInfo_r16__measResultNeighCells_r16__Type ->
  measResultListLogging2NR_r16__Type option * (measResultList2EUTRA_r16__Type
  option * unit)

val logMeasInfo_r16__measResultNeighCells_r16__F2 :
  seq_type -> logMeasInfo_r16__measResultNeighCells_r16__Type

val logMeasInfo_r16__measResultNeighCells_r16__Format :
  logMeasInfo_r16__measResultNeighCells_r16__Type t_Format

val logMeasInfo_r16__anyCellSelectionDetected_r16__Format :
  logMeasInfo_r16__anyCellSelectionDetected_r16__Type t_Format

val logMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__Format :
  logMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__Type t_Format

type logMeasInfo_r16__ext0O__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val logMeasInfo_r16__ext0O__Format_list : logMeasInfo_r16__ext0O__Format_Type

val logMeasInfo_r16__ext0O__list__Format : seq_type t_Format

val logMeasInfo_r16__ext0O__F1 :
  logMeasInfo_r16__ext0O__Type ->
  logMeasInfo_r16__ext0O__inDeviceCoexDetected_r17__Type option * unit

val logMeasInfo_r16__ext0O__F2 : seq_type -> logMeasInfo_r16__ext0O__Type

val logMeasInfo_r16__ext0O__Format : logMeasInfo_r16__ext0O__Type t_Format

val logMeasInfo_r16__ext0__check_all_none :
  logMeasInfo_r16__ext0O__Type -> bool

val logMeasInfo_r16__ext0__Format : logMeasInfo_r16__ext0__Type t_Format

type logMeasInfo_r16__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))))

val logMeasInfo_r16__root_Format_list : logMeasInfo_r16__root_Format_Type

type logMeasInfo_r16__ext_Format_Type =
  logMeasInfo_r16__ext0__Type t_Format * unit t_Format

val logMeasInfo_r16__ext_Format_list : logMeasInfo_r16__ext_Format_Type

type logMeasInfo_r16__list_type = seq_type * seq_ext_type

val logMeasInfo_r16__list_format : logMeasInfo_r16__list_type t_Format

val logMeasInfo_r16__F1 : logMeasInfo_r16__Type -> logMeasInfo_r16__list_type

val logMeasInfo_r16__F2 : logMeasInfo_r16__list_type -> logMeasInfo_r16__Type

val logMeasInfo_r16__Format : logMeasInfo_r16__Type t_Format

type logMeasInfoList_r16__Type = logMeasInfo_r16__Type list

val logMeasInfoList_r16__Format : logMeasInfoList_r16__Type t_Format

type logMeasReport_r16__traceRecordingSessionRef_r16__Type = octet_string

type logMeasReport_r16__tce_Id_r16__Type = octet_string

type logMeasReport_r16__logMeasAvailable_r16__Type =
| LogMeasReport_r16__logMeasAvailable_r16__true

val logMeasReport_r16__logMeasAvailable_r16__nat__Format : int t_Format

val logMeasReport_r16__logMeasAvailable_r16__F1 :
  logMeasReport_r16__logMeasAvailable_r16__Type -> int

val logMeasReport_r16__logMeasAvailable_r16__F2 :
  int -> logMeasReport_r16__logMeasAvailable_r16__Type

type logMeasReport_r16__logMeasAvailableBT_r16__Type =
| LogMeasReport_r16__logMeasAvailableBT_r16__true

val logMeasReport_r16__logMeasAvailableBT_r16__nat__Format : int t_Format

val logMeasReport_r16__logMeasAvailableBT_r16__F1 :
  logMeasReport_r16__logMeasAvailableBT_r16__Type -> int

val logMeasReport_r16__logMeasAvailableBT_r16__F2 :
  int -> logMeasReport_r16__logMeasAvailableBT_r16__Type

type logMeasReport_r16__logMeasAvailableWLAN_r16__Type =
| LogMeasReport_r16__logMeasAvailableWLAN_r16__true

val logMeasReport_r16__logMeasAvailableWLAN_r16__nat__Format : int t_Format

val logMeasReport_r16__logMeasAvailableWLAN_r16__F1 :
  logMeasReport_r16__logMeasAvailableWLAN_r16__Type -> int

val logMeasReport_r16__logMeasAvailableWLAN_r16__F2 :
  int -> logMeasReport_r16__logMeasAvailableWLAN_r16__Type

type logMeasReport_r16__Type = { logMeasReport_r16__absoluteTimeStamp_r16 : 
                                 absoluteTimeInfo_r16__Type;
                                 logMeasReport_r16__traceReference_r16 : 
                                 traceReference_r16__Type;
                                 logMeasReport_r16__traceRecordingSessionRef_r16 : 
                                 logMeasReport_r16__traceRecordingSessionRef_r16__Type;
                                 logMeasReport_r16__tce_Id_r16 : logMeasReport_r16__tce_Id_r16__Type;
                                 logMeasReport_r16__logMeasInfoList_r16 : 
                                 logMeasInfoList_r16__Type;
                                 logMeasReport_r16__logMeasAvailable_r16 : 
                                 logMeasReport_r16__logMeasAvailable_r16__Type
                                 option;
                                 logMeasReport_r16__logMeasAvailableBT_r16 : 
                                 logMeasReport_r16__logMeasAvailableBT_r16__Type
                                 option;
                                 logMeasReport_r16__logMeasAvailableWLAN_r16 : 
                                 logMeasReport_r16__logMeasAvailableWLAN_r16__Type
                                 option }

val logMeasReport_r16__root_list : seq_elem list

val logMeasReport_r16__ext_list : typ list

val logMeasReport_r16__traceRecordingSessionRef_r16__Format :
  logMeasReport_r16__traceRecordingSessionRef_r16__Type t_Format

val logMeasReport_r16__tce_Id_r16__Format :
  logMeasReport_r16__tce_Id_r16__Type t_Format

val logMeasReport_r16__logMeasAvailable_r16__Format :
  logMeasReport_r16__logMeasAvailable_r16__Type t_Format

val logMeasReport_r16__logMeasAvailableBT_r16__Format :
  logMeasReport_r16__logMeasAvailableBT_r16__Type t_Format

val logMeasReport_r16__logMeasAvailableWLAN_r16__Format :
  logMeasReport_r16__logMeasAvailableWLAN_r16__Type t_Format

type logMeasReport_r16__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))))))

val logMeasReport_r16__root_Format_list : logMeasReport_r16__root_Format_Type

type logMeasReport_r16__ext_Format_Type = unit t_Format

val logMeasReport_r16__ext_Format_list : logMeasReport_r16__ext_Format_Type

type logMeasReport_r16__list_type = seq_type * seq_ext_type

val logMeasReport_r16__list_format : logMeasReport_r16__list_type t_Format

val logMeasReport_r16__F1 :
  logMeasReport_r16__Type -> logMeasReport_r16__list_type

val logMeasReport_r16__F2 :
  logMeasReport_r16__list_type -> logMeasReport_r16__Type

val logMeasReport_r16__Format : logMeasReport_r16__Type t_Format

type measResultFailedCell_r16__measResult_r16__cellResults_r16__Type = { 
measResultFailedCell_r16__measResult_r16__cellResults_r16__resultsSSB_Cell_r16 : 
measQuantityResults__Type }

val measResultFailedCell_r16__measResult_r16__cellResults_r16__list :
  seq_elem list

type measResultFailedCell_r16__measResult_r16__rsIndexResults_r16__Type = { 
measResultFailedCell_r16__measResult_r16__rsIndexResults_r16__resultsSSB_Indexes_r16 : 
resultsPerSSB_IndexList__Type }

val measResultFailedCell_r16__measResult_r16__rsIndexResults_r16__list :
  seq_elem list

type measResultFailedCell_r16__measResult_r16__Type = { measResultFailedCell_r16__measResult_r16__cellResults_r16 : 
                                                        measResultFailedCell_r16__measResult_r16__cellResults_r16__Type;
                                                        measResultFailedCell_r16__measResult_r16__rsIndexResults_r16 : 
                                                        measResultFailedCell_r16__measResult_r16__rsIndexResults_r16__Type }

val measResultFailedCell_r16__measResult_r16__list : seq_elem list

type measResultFailedCell_r16__Type = { measResultFailedCell_r16__cgi_Info : 
                                        cGI_Info_Logging_r16__Type;
                                        measResultFailedCell_r16__measResult_r16 : 
                                        measResultFailedCell_r16__measResult_r16__Type }

val measResultFailedCell_r16__list : seq_elem list

type measResultFailedCell_r16__measResult_r16__cellResults_r16__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val measResultFailedCell_r16__measResult_r16__cellResults_r16__Format_list :
  measResultFailedCell_r16__measResult_r16__cellResults_r16__Format_Type

val measResultFailedCell_r16__measResult_r16__cellResults_r16__list__Format :
  seq_type t_Format

val measResultFailedCell_r16__measResult_r16__cellResults_r16__F1 :
  measResultFailedCell_r16__measResult_r16__cellResults_r16__Type ->
  measQuantityResults__Type * unit

val measResultFailedCell_r16__measResult_r16__cellResults_r16__F2 :
  seq_type -> measResultFailedCell_r16__measResult_r16__cellResults_r16__Type

val measResultFailedCell_r16__measResult_r16__cellResults_r16__Format :
  measResultFailedCell_r16__measResult_r16__cellResults_r16__Type t_Format

type measResultFailedCell_r16__measResult_r16__rsIndexResults_r16__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val measResultFailedCell_r16__measResult_r16__rsIndexResults_r16__Format_list :
  measResultFailedCell_r16__measResult_r16__rsIndexResults_r16__Format_Type

val measResultFailedCell_r16__measResult_r16__rsIndexResults_r16__list__Format :
  seq_type t_Format

val measResultFailedCell_r16__measResult_r16__rsIndexResults_r16__F1 :
  measResultFailedCell_r16__measResult_r16__rsIndexResults_r16__Type ->
  resultsPerSSB_IndexList__Type * unit

val measResultFailedCell_r16__measResult_r16__rsIndexResults_r16__F2 :
  seq_type ->
  measResultFailedCell_r16__measResult_r16__rsIndexResults_r16__Type

val measResultFailedCell_r16__measResult_r16__rsIndexResults_r16__Format :
  measResultFailedCell_r16__measResult_r16__rsIndexResults_r16__Type t_Format

type measResultFailedCell_r16__measResult_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val measResultFailedCell_r16__measResult_r16__Format_list :
  measResultFailedCell_r16__measResult_r16__Format_Type

val measResultFailedCell_r16__measResult_r16__list__Format : seq_type t_Format

val measResultFailedCell_r16__measResult_r16__F1 :
  measResultFailedCell_r16__measResult_r16__Type ->
  measResultFailedCell_r16__measResult_r16__cellResults_r16__Type * (measResultFailedCell_r16__measResult_r16__rsIndexResults_r16__Type * unit)

val measResultFailedCell_r16__measResult_r16__F2 :
  seq_type -> measResultFailedCell_r16__measResult_r16__Type

val measResultFailedCell_r16__measResult_r16__Format :
  measResultFailedCell_r16__measResult_r16__Type t_Format

type measResultFailedCell_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val measResultFailedCell_r16__Format_list :
  measResultFailedCell_r16__Format_Type

val measResultFailedCell_r16__list__Format : seq_type t_Format

val measResultFailedCell_r16__F1 :
  measResultFailedCell_r16__Type ->
  cGI_Info_Logging_r16__Type * (measResultFailedCell_r16__measResult_r16__Type * unit)

val measResultFailedCell_r16__F2 : seq_type -> measResultFailedCell_r16__Type

val measResultFailedCell_r16__Format : measResultFailedCell_r16__Type t_Format

type measResult2NR_r16__Type = { measResult2NR_r16__ssbFrequency_r16 : 
                                 aRFCN_ValueNR__Type option;
                                 measResult2NR_r16__refFreqCSI_RS_r16 : 
                                 aRFCN_ValueNR__Type option;
                                 measResult2NR_r16__measResultList_r16 : 
                                 measResultListNR__Type }

val measResult2NR_r16__list : seq_elem list

type measResult2NR_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val measResult2NR_r16__Format_list : measResult2NR_r16__Format_Type

val measResult2NR_r16__list__Format : seq_type t_Format

val measResult2NR_r16__F1 :
  measResult2NR_r16__Type -> aRFCN_ValueNR__Type option * (aRFCN_ValueNR__Type
  option * (measResultListNR__Type * unit))

val measResult2NR_r16__F2 : seq_type -> measResult2NR_r16__Type

val measResult2NR_r16__Format : measResult2NR_r16__Type t_Format

type measResultList2NR_r16__Type = measResult2NR_r16__Type list

val measResultList2NR_r16__Format : measResultList2NR_r16__Type t_Format

type timeSinceFailure_r16__Type = int

val timeSinceFailure_r16__Format : int t_Format

type connEstFailReport_r16__measResultNeighCells_r16__Type = { connEstFailReport_r16__measResultNeighCells_r16__measResultNeighCellListNR : 
                                                               measResultList2NR_r16__Type
                                                               option;
                                                               connEstFailReport_r16__measResultNeighCells_r16__measResultNeighCellListEUTRA : 
                                                               measResultList2EUTRA_r16__Type
                                                               option }

val connEstFailReport_r16__measResultNeighCells_r16__list : seq_elem list

type connEstFailReport_r16__Type = { connEstFailReport_r16__measResultFailedCell_r16 : 
                                     measResultFailedCell_r16__Type;
                                     connEstFailReport_r16__locationInfo_r16 : 
                                     locationInfo_r16__Type option;
                                     connEstFailReport_r16__measResultNeighCells_r16 : 
                                     connEstFailReport_r16__measResultNeighCells_r16__Type;
                                     connEstFailReport_r16__numberOfConnFail_r16 : 
                                     int;
                                     connEstFailReport_r16__perRAInfoList_r16 : 
                                     perRAInfoList_r16__Type;
                                     connEstFailReport_r16__timeSinceFailure_r16 : 
                                     timeSinceFailure_r16__Type }

val connEstFailReport_r16__root_list : seq_elem list

val connEstFailReport_r16__ext_list : typ list

type connEstFailReport_r16__measResultNeighCells_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val connEstFailReport_r16__measResultNeighCells_r16__Format_list :
  connEstFailReport_r16__measResultNeighCells_r16__Format_Type

val connEstFailReport_r16__measResultNeighCells_r16__list__Format :
  seq_type t_Format

val connEstFailReport_r16__measResultNeighCells_r16__F1 :
  connEstFailReport_r16__measResultNeighCells_r16__Type ->
  measResultList2NR_r16__Type option * (measResultList2EUTRA_r16__Type
  option * unit)

val connEstFailReport_r16__measResultNeighCells_r16__F2 :
  seq_type -> connEstFailReport_r16__measResultNeighCells_r16__Type

val connEstFailReport_r16__measResultNeighCells_r16__Format :
  connEstFailReport_r16__measResultNeighCells_r16__Type t_Format

val connEstFailReport_r16__numberOfConnFail_r16__Format : int t_Format

type connEstFailReport_r16__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))))

val connEstFailReport_r16__root_Format_list :
  connEstFailReport_r16__root_Format_Type

type connEstFailReport_r16__ext_Format_Type = unit t_Format

val connEstFailReport_r16__ext_Format_list :
  connEstFailReport_r16__ext_Format_Type

type connEstFailReport_r16__list_type = seq_type * seq_ext_type

val connEstFailReport_r16__list_format :
  connEstFailReport_r16__list_type t_Format

val connEstFailReport_r16__F1 :
  connEstFailReport_r16__Type -> connEstFailReport_r16__list_type

val connEstFailReport_r16__F2 :
  connEstFailReport_r16__list_type -> connEstFailReport_r16__Type

val connEstFailReport_r16__Format : connEstFailReport_r16__Type t_Format

type pCI_ARFCN_NR_r16__Type = { pCI_ARFCN_NR_r16__physCellId_r16 : physCellId__Type;
                                pCI_ARFCN_NR_r16__carrierFreq_r16 : aRFCN_ValueNR__Type }

val pCI_ARFCN_NR_r16__list : seq_elem list

type pCI_ARFCN_NR_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val pCI_ARFCN_NR_r16__Format_list : pCI_ARFCN_NR_r16__Format_Type

val pCI_ARFCN_NR_r16__list__Format : seq_type t_Format

val pCI_ARFCN_NR_r16__F1 :
  pCI_ARFCN_NR_r16__Type -> physCellId__Type * (aRFCN_ValueNR__Type * unit)

val pCI_ARFCN_NR_r16__F2 : seq_type -> pCI_ARFCN_NR_r16__Type

val pCI_ARFCN_NR_r16__Format : pCI_ARFCN_NR_r16__Type t_Format

type subcarrierSpacing__Type =
| SubcarrierSpacing__kHz15
| SubcarrierSpacing__kHz30
| SubcarrierSpacing__kHz60
| SubcarrierSpacing__kHz120
| SubcarrierSpacing__kHz240
| SubcarrierSpacing__kHz480_v1700
| SubcarrierSpacing__kHz960_v1700
| SubcarrierSpacing__spare1

val subcarrierSpacing__nat__Format : int t_Format

val subcarrierSpacing__F1 : subcarrierSpacing__Type -> int

val subcarrierSpacing__F2 : int -> subcarrierSpacing__Type

val subcarrierSpacing__Format : subcarrierSpacing__Type t_Format

type perRACSI_RSInfo_v1660__Type = { perRACSI_RSInfo_v1660__csi_RS_Index_v1660 : 
                                     int option }

val perRACSI_RSInfo_v1660__list : seq_elem list

val perRACSI_RSInfo_v1660__csi_RS_Index_v1660__Format : int t_Format

type perRACSI_RSInfo_v1660__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val perRACSI_RSInfo_v1660__Format_list : perRACSI_RSInfo_v1660__Format_Type

val perRACSI_RSInfo_v1660__list__Format : seq_type t_Format

val perRACSI_RSInfo_v1660__F1 :
  perRACSI_RSInfo_v1660__Type -> int option * unit

val perRACSI_RSInfo_v1660__F2 : seq_type -> perRACSI_RSInfo_v1660__Type

val perRACSI_RSInfo_v1660__Format : perRACSI_RSInfo_v1660__Type t_Format

type perRAInfoList_v1660__Type = perRACSI_RSInfo_v1660__Type list

val perRAInfoList_v1660__Format : perRAInfoList_v1660__Type t_Format

type sIB_Type_r17__Type =
| SIB_Type_r17__sibType2
| SIB_Type_r17__sibType3
| SIB_Type_r17__sibType4
| SIB_Type_r17__sibType5
| SIB_Type_r17__sibType9
| SIB_Type_r17__sibType10_v1610
| SIB_Type_r17__sibType11_v1610
| SIB_Type_r17__sibType12_v1610
| SIB_Type_r17__sibType13_v1610
| SIB_Type_r17__sibType14_v1610
| SIB_Type_r17__spare6
| SIB_Type_r17__spare5
| SIB_Type_r17__spare4
| SIB_Type_r17__spare3
| SIB_Type_r17__spare2
| SIB_Type_r17__spare1

val sIB_Type_r17__nat__Format : int t_Format

val sIB_Type_r17__F1 : sIB_Type_r17__Type -> int

val sIB_Type_r17__F2 : int -> sIB_Type_r17__Type

val sIB_Type_r17__Format : sIB_Type_r17__Type t_Format

type rA_InformationCommon_r16__msg1_FDM_r16__Type =
| RA_InformationCommon_r16__msg1_FDM_r16__one
| RA_InformationCommon_r16__msg1_FDM_r16__two
| RA_InformationCommon_r16__msg1_FDM_r16__four
| RA_InformationCommon_r16__msg1_FDM_r16__eight

val rA_InformationCommon_r16__msg1_FDM_r16__nat__Format : int t_Format

val rA_InformationCommon_r16__msg1_FDM_r16__F1 :
  rA_InformationCommon_r16__msg1_FDM_r16__Type -> int

val rA_InformationCommon_r16__msg1_FDM_r16__F2 :
  int -> rA_InformationCommon_r16__msg1_FDM_r16__Type

type rA_InformationCommon_r16__msg1_FDMCFRA_r16__Type =
| RA_InformationCommon_r16__msg1_FDMCFRA_r16__one
| RA_InformationCommon_r16__msg1_FDMCFRA_r16__two
| RA_InformationCommon_r16__msg1_FDMCFRA_r16__four
| RA_InformationCommon_r16__msg1_FDMCFRA_r16__eight

val rA_InformationCommon_r16__msg1_FDMCFRA_r16__nat__Format : int t_Format

val rA_InformationCommon_r16__msg1_FDMCFRA_r16__F1 :
  rA_InformationCommon_r16__msg1_FDMCFRA_r16__Type -> int

val rA_InformationCommon_r16__msg1_FDMCFRA_r16__F2 :
  int -> rA_InformationCommon_r16__msg1_FDMCFRA_r16__Type

type rA_InformationCommon_r16__ext0O__Type = { rA_InformationCommon_r16__ext0O__perRAInfoList_v1660 : 
                                               perRAInfoList_v1660__Type option }

val rA_InformationCommon_r16__ext0O__list : seq_elem list

type rA_InformationCommon_r16__ext0__Type =
  rA_InformationCommon_r16__ext0O__Type

type rA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__Type =
| RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__kHz1dot25
| RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__kHz5
| RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__spare2
| RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__spare1

val rA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__nat__Format :
  int t_Format

val rA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__F1 :
  rA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__Type
  -> int

val rA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__F2 :
  int ->
  rA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__Type

type rA_InformationCommon_r16__ext1O__Type = { rA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16 : 
                                               rA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__Type
                                               option }

val rA_InformationCommon_r16__ext1O__list : seq_elem list

type rA_InformationCommon_r16__ext1__Type =
  rA_InformationCommon_r16__ext1O__Type

type rA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__Type =
| RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__kHz1dot25
| RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__kHz5
| RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__spare2
| RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__spare1

val rA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__nat__Format :
  int t_Format

val rA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__F1 :
  rA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__Type
  -> int

val rA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__F2 :
  int ->
  rA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__Type

type rA_InformationCommon_r16__ext2O__Type = { rA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16 : 
                                               rA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__Type
                                               option }

val rA_InformationCommon_r16__ext2O__list : seq_elem list

type rA_InformationCommon_r16__ext2__Type =
  rA_InformationCommon_r16__ext2O__Type

type rA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__Type =
| RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__one
| RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__two
| RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__four
| RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__eight

val rA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__nat__Format :
  int t_Format

val rA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__F1 :
  rA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__Type -> int

val rA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__F2 :
  int -> rA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__Type

type rA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__Type =
| RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__one
| RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__two
| RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__four
| RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__eight

val rA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__nat__Format :
  int t_Format

val rA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__F1 :
  rA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__Type -> int

val rA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__F2 :
  int -> rA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__Type

type rA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__Type =
| RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__kHz1dot25
| RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__kHz5
| RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__spare2
| RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__spare1

val rA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__nat__Format :
  int t_Format

val rA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__F1 :
  rA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__Type
  -> int

val rA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__F2 :
  int ->
  rA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__Type

type rA_InformationCommon_r16__ext3O__msgA_TransMax_r17__Type =
| RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n1
| RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n2
| RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n4
| RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n6
| RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n8
| RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n10
| RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n20
| RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n50
| RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n100
| RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n200

val rA_InformationCommon_r16__ext3O__msgA_TransMax_r17__nat__Format :
  int t_Format

val rA_InformationCommon_r16__ext3O__msgA_TransMax_r17__F1 :
  rA_InformationCommon_r16__ext3O__msgA_TransMax_r17__Type -> int

val rA_InformationCommon_r16__ext3O__msgA_TransMax_r17__F2 :
  int -> rA_InformationCommon_r16__ext3O__msgA_TransMax_r17__Type

type rA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__Type =
| RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__one
| RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__two
| RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__four
| RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__eight

val rA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__nat__Format :
  int t_Format

val rA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__F1 :
  rA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__Type -> int

val rA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__F2 :
  int -> rA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__Type

type rA_InformationCommon_r16__ext3O__intendedSIBs_r17__Type =
  sIB_Type_r17__Type list

type rA_InformationCommon_r16__ext3O__ssbsForSI_Acquisition_r17__Type =
  sSB_Index__Type list

type rA_InformationCommon_r16__ext3O__msgA_PUSCH_PayloadSize_r17__Type =
  bit_string_fixed

type rA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__Type =
| RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__true

val rA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__nat__Format :
  int t_Format

val rA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__F1 :
  rA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__Type -> int

val rA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__F2 :
  int -> rA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__Type

type rA_InformationCommon_r16__ext3O__Type = { rA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStart_r17 : 
                                               int option;
                                               rA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStartCFRA_r17 : 
                                               int option;
                                               rA_InformationCommon_r16__ext3O__msgA_SubcarrierSpacing_r17 : 
                                               subcarrierSpacing__Type option;
                                               rA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17 : 
                                               rA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__Type
                                               option;
                                               rA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17 : 
                                               rA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__Type
                                               option;
                                               rA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17 : 
                                               rA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__Type
                                               option;
                                               rA_InformationCommon_r16__ext3O__msgA_TransMax_r17 : 
                                               rA_InformationCommon_r16__ext3O__msgA_TransMax_r17__Type
                                               option;
                                               rA_InformationCommon_r16__ext3O__msgA_MCS_r17 : 
                                               int option;
                                               rA_InformationCommon_r16__ext3O__nrofPRBs_PerMsgA_PO_r17 : 
                                               int option;
                                               rA_InformationCommon_r16__ext3O__msgA_PUSCH_TimeDomainAllocation_r17 : 
                                               int option;
                                               rA_InformationCommon_r16__ext3O__frequencyStartMsgA_PUSCH_r17 : 
                                               int option;
                                               rA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17 : 
                                               rA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__Type
                                               option;
                                               rA_InformationCommon_r16__ext3O__dlPathlossRSRP_r17 : 
                                               rSRP_Range__Type option;
                                               rA_InformationCommon_r16__ext3O__intendedSIBs_r17 : 
                                               rA_InformationCommon_r16__ext3O__intendedSIBs_r17__Type
                                               option;
                                               rA_InformationCommon_r16__ext3O__ssbsForSI_Acquisition_r17 : 
                                               rA_InformationCommon_r16__ext3O__ssbsForSI_Acquisition_r17__Type
                                               option;
                                               rA_InformationCommon_r16__ext3O__msgA_PUSCH_PayloadSize_r17 : 
                                               rA_InformationCommon_r16__ext3O__msgA_PUSCH_PayloadSize_r17__Type
                                               option;
                                               rA_InformationCommon_r16__ext3O__onDemandSISuccess_r17 : 
                                               rA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__Type
                                               option }

val rA_InformationCommon_r16__ext3O__list : seq_elem list

type rA_InformationCommon_r16__ext3__Type =
  rA_InformationCommon_r16__ext3O__Type

type rA_InformationCommon_r16__Type = { rA_InformationCommon_r16__absoluteFrequencyPointA_r16 : 
                                        aRFCN_ValueNR__Type;
                                        rA_InformationCommon_r16__locationAndBandwidth_r16 : 
                                        int;
                                        rA_InformationCommon_r16__subcarrierSpacing_r16 : 
                                        subcarrierSpacing__Type;
                                        rA_InformationCommon_r16__msg1_FrequencyStart_r16 : 
                                        int option;
                                        rA_InformationCommon_r16__msg1_FrequencyStartCFRA_r16 : 
                                        int option;
                                        rA_InformationCommon_r16__msg1_SubcarrierSpacing_r16 : 
                                        subcarrierSpacing__Type option;
                                        rA_InformationCommon_r16__msg1_SubcarrierSpacingCFRA_r16 : 
                                        subcarrierSpacing__Type option;
                                        rA_InformationCommon_r16__msg1_FDM_r16 : 
                                        rA_InformationCommon_r16__msg1_FDM_r16__Type
                                        option;
                                        rA_InformationCommon_r16__msg1_FDMCFRA_r16 : 
                                        rA_InformationCommon_r16__msg1_FDMCFRA_r16__Type
                                        option;
                                        rA_InformationCommon_r16__perRAInfoList_r16 : 
                                        perRAInfoList_r16__Type;
                                        rA_InformationCommon_r16__ext0 : 
                                        rA_InformationCommon_r16__ext0__Type
                                        option;
                                        rA_InformationCommon_r16__ext1 : 
                                        rA_InformationCommon_r16__ext1__Type
                                        option;
                                        rA_InformationCommon_r16__ext2 : 
                                        rA_InformationCommon_r16__ext2__Type
                                        option;
                                        rA_InformationCommon_r16__ext3 : 
                                        rA_InformationCommon_r16__ext3__Type
                                        option }

val rA_InformationCommon_r16__root_list : seq_elem list

val rA_InformationCommon_r16__ext_list : typ list

val rA_InformationCommon_r16__locationAndBandwidth_r16__Format : int t_Format

val rA_InformationCommon_r16__msg1_FrequencyStart_r16__Format : int t_Format

val rA_InformationCommon_r16__msg1_FrequencyStartCFRA_r16__Format :
  int t_Format

val rA_InformationCommon_r16__msg1_FDM_r16__Format :
  rA_InformationCommon_r16__msg1_FDM_r16__Type t_Format

val rA_InformationCommon_r16__msg1_FDMCFRA_r16__Format :
  rA_InformationCommon_r16__msg1_FDMCFRA_r16__Type t_Format

type rA_InformationCommon_r16__ext0O__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val rA_InformationCommon_r16__ext0O__Format_list :
  rA_InformationCommon_r16__ext0O__Format_Type

val rA_InformationCommon_r16__ext0O__list__Format : seq_type t_Format

val rA_InformationCommon_r16__ext0O__F1 :
  rA_InformationCommon_r16__ext0O__Type -> perRAInfoList_v1660__Type
  option * unit

val rA_InformationCommon_r16__ext0O__F2 :
  seq_type -> rA_InformationCommon_r16__ext0O__Type

val rA_InformationCommon_r16__ext0O__Format :
  rA_InformationCommon_r16__ext0O__Type t_Format

val rA_InformationCommon_r16__ext0__check_all_none :
  rA_InformationCommon_r16__ext0O__Type -> bool

val rA_InformationCommon_r16__ext0__Format :
  rA_InformationCommon_r16__ext0__Type t_Format

val rA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__Format :
  rA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__Type
  t_Format

type rA_InformationCommon_r16__ext1O__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val rA_InformationCommon_r16__ext1O__Format_list :
  rA_InformationCommon_r16__ext1O__Format_Type

val rA_InformationCommon_r16__ext1O__list__Format : seq_type t_Format

val rA_InformationCommon_r16__ext1O__F1 :
  rA_InformationCommon_r16__ext1O__Type ->
  rA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__Type
  option * unit

val rA_InformationCommon_r16__ext1O__F2 :
  seq_type -> rA_InformationCommon_r16__ext1O__Type

val rA_InformationCommon_r16__ext1O__Format :
  rA_InformationCommon_r16__ext1O__Type t_Format

val rA_InformationCommon_r16__ext1__check_all_none :
  rA_InformationCommon_r16__ext1O__Type -> bool

val rA_InformationCommon_r16__ext1__Format :
  rA_InformationCommon_r16__ext1__Type t_Format

val rA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__Format :
  rA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__Type
  t_Format

type rA_InformationCommon_r16__ext2O__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val rA_InformationCommon_r16__ext2O__Format_list :
  rA_InformationCommon_r16__ext2O__Format_Type

val rA_InformationCommon_r16__ext2O__list__Format : seq_type t_Format

val rA_InformationCommon_r16__ext2O__F1 :
  rA_InformationCommon_r16__ext2O__Type ->
  rA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__Type
  option * unit

val rA_InformationCommon_r16__ext2O__F2 :
  seq_type -> rA_InformationCommon_r16__ext2O__Type

val rA_InformationCommon_r16__ext2O__Format :
  rA_InformationCommon_r16__ext2O__Type t_Format

val rA_InformationCommon_r16__ext2__check_all_none :
  rA_InformationCommon_r16__ext2O__Type -> bool

val rA_InformationCommon_r16__ext2__Format :
  rA_InformationCommon_r16__ext2__Type t_Format

val rA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStart_r17__Format :
  int t_Format

val rA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStartCFRA_r17__Format :
  int t_Format

val rA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__Format :
  rA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__Type t_Format

val rA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__Format :
  rA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__Type t_Format

val rA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__Format :
  rA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__Type
  t_Format

val rA_InformationCommon_r16__ext3O__msgA_TransMax_r17__Format :
  rA_InformationCommon_r16__ext3O__msgA_TransMax_r17__Type t_Format

val rA_InformationCommon_r16__ext3O__msgA_MCS_r17__Format : int t_Format

val rA_InformationCommon_r16__ext3O__nrofPRBs_PerMsgA_PO_r17__Format :
  int t_Format

val rA_InformationCommon_r16__ext3O__msgA_PUSCH_TimeDomainAllocation_r17__Format :
  int t_Format

val rA_InformationCommon_r16__ext3O__frequencyStartMsgA_PUSCH_r17__Format :
  int t_Format

val rA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__Format :
  rA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__Type t_Format

val rA_InformationCommon_r16__ext3O__intendedSIBs_r17__Format :
  rA_InformationCommon_r16__ext3O__intendedSIBs_r17__Type t_Format

val rA_InformationCommon_r16__ext3O__ssbsForSI_Acquisition_r17__Format :
  rA_InformationCommon_r16__ext3O__ssbsForSI_Acquisition_r17__Type t_Format

val rA_InformationCommon_r16__ext3O__msgA_PUSCH_PayloadSize_r17__Format :
  rA_InformationCommon_r16__ext3O__msgA_PUSCH_PayloadSize_r17__Type t_Format

val rA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__Format :
  rA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__Type t_Format

type rA_InformationCommon_r16__ext3O__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))))))))))))))))

val rA_InformationCommon_r16__ext3O__Format_list :
  rA_InformationCommon_r16__ext3O__Format_Type

val rA_InformationCommon_r16__ext3O__list__Format : seq_type t_Format

val rA_InformationCommon_r16__ext3O__F1 :
  rA_InformationCommon_r16__ext3O__Type -> int option * (int
  option * (subcarrierSpacing__Type
  option * (rA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__Type
  option * (rA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__Type
  option * (rA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__Type
  option * (rA_InformationCommon_r16__ext3O__msgA_TransMax_r17__Type
  option * (int option * (int option * (int option * (int
  option * (rA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__Type
  option * (rSRP_Range__Type
  option * (rA_InformationCommon_r16__ext3O__intendedSIBs_r17__Type
  option * (rA_InformationCommon_r16__ext3O__ssbsForSI_Acquisition_r17__Type
  option * (rA_InformationCommon_r16__ext3O__msgA_PUSCH_PayloadSize_r17__Type
  option * (rA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__Type
  option * unit))))))))))))))))

val rA_InformationCommon_r16__ext3O__F2 :
  seq_type -> rA_InformationCommon_r16__ext3O__Type

val rA_InformationCommon_r16__ext3O__Format :
  rA_InformationCommon_r16__ext3O__Type t_Format

val rA_InformationCommon_r16__ext3__check_all_none :
  rA_InformationCommon_r16__ext3O__Type -> bool

val rA_InformationCommon_r16__ext3__Format :
  rA_InformationCommon_r16__ext3__Type t_Format

type rA_InformationCommon_r16__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))))))))

val rA_InformationCommon_r16__root_Format_list :
  rA_InformationCommon_r16__root_Format_Type

type rA_InformationCommon_r16__ext_Format_Type =
  rA_InformationCommon_r16__ext0__Type
  t_Format * (rA_InformationCommon_r16__ext1__Type
  t_Format * (rA_InformationCommon_r16__ext2__Type
  t_Format * (rA_InformationCommon_r16__ext3__Type t_Format * unit t_Format)))

val rA_InformationCommon_r16__ext_Format_list :
  rA_InformationCommon_r16__ext_Format_Type

type rA_InformationCommon_r16__list_type = seq_type * seq_ext_type

val rA_InformationCommon_r16__list_format :
  rA_InformationCommon_r16__list_type t_Format

val rA_InformationCommon_r16__F1 :
  rA_InformationCommon_r16__Type -> rA_InformationCommon_r16__list_type

val rA_InformationCommon_r16__F2 :
  rA_InformationCommon_r16__list_type -> rA_InformationCommon_r16__Type

val rA_InformationCommon_r16__Format : rA_InformationCommon_r16__Type t_Format

type rA_Report_r16__cellId_r16__Type =
| RA_Report_r16__cellId_r16__cellGlobalId_r16 of cGI_Info_Logging_r16__Type
| RA_Report_r16__cellId_r16__pci_arfcn_r16 of pCI_ARFCN_NR_r16__Type

type rA_Report_r16__raPurpose_r16__Type =
| RA_Report_r16__raPurpose_r16__accessRelated
| RA_Report_r16__raPurpose_r16__beamFailureRecovery
| RA_Report_r16__raPurpose_r16__reconfigurationWithSync
| RA_Report_r16__raPurpose_r16__ulUnSynchronized
| RA_Report_r16__raPurpose_r16__schedulingRequestFailure
| RA_Report_r16__raPurpose_r16__noPUCCHResourceAvailable
| RA_Report_r16__raPurpose_r16__requestForOtherSI
| RA_Report_r16__raPurpose_r16__msg3RequestForOtherSI_r17
| RA_Report_r16__raPurpose_r16__spare8
| RA_Report_r16__raPurpose_r16__spare7
| RA_Report_r16__raPurpose_r16__spare6
| RA_Report_r16__raPurpose_r16__spare5
| RA_Report_r16__raPurpose_r16__spare4
| RA_Report_r16__raPurpose_r16__spare3
| RA_Report_r16__raPurpose_r16__spare2
| RA_Report_r16__raPurpose_r16__spare1

val rA_Report_r16__raPurpose_r16__nat__Format : int t_Format

val rA_Report_r16__raPurpose_r16__F1 :
  rA_Report_r16__raPurpose_r16__Type -> int

val rA_Report_r16__raPurpose_r16__F2 :
  int -> rA_Report_r16__raPurpose_r16__Type

type rA_Report_r16__ext0O__Type = { rA_Report_r16__ext0O__spCellID_r17 : 
                                    cGI_Info_Logging_r16__Type option }

val rA_Report_r16__ext0O__list : seq_elem list

type rA_Report_r16__ext0__Type = rA_Report_r16__ext0O__Type

type rA_Report_r16__Type = { rA_Report_r16__cellId_r16 : rA_Report_r16__cellId_r16__Type;
                             rA_Report_r16__ra_InformationCommon_r16 : 
                             rA_InformationCommon_r16__Type option;
                             rA_Report_r16__raPurpose_r16 : rA_Report_r16__raPurpose_r16__Type;
                             rA_Report_r16__ext0 : rA_Report_r16__ext0__Type
                                                   option }

val rA_Report_r16__root_list : seq_elem list

val rA_Report_r16__ext_list : typ list

val rA_Report_r16__cellId_r16__list__Format : (int, __) sigT t_Format

val rA_Report_r16__cellId_r16__F1 : rA_Report_r16__cellId_r16__Type -> choice

val rA_Report_r16__cellId_r16__F2 : choice -> rA_Report_r16__cellId_r16__Type

val rA_Report_r16__cellId_r16__Format :
  rA_Report_r16__cellId_r16__Type t_Format

val rA_Report_r16__raPurpose_r16__Format :
  rA_Report_r16__raPurpose_r16__Type t_Format

type rA_Report_r16__ext0O__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val rA_Report_r16__ext0O__Format_list : rA_Report_r16__ext0O__Format_Type

val rA_Report_r16__ext0O__list__Format : seq_type t_Format

val rA_Report_r16__ext0O__F1 :
  rA_Report_r16__ext0O__Type -> cGI_Info_Logging_r16__Type option * unit

val rA_Report_r16__ext0O__F2 : seq_type -> rA_Report_r16__ext0O__Type

val rA_Report_r16__ext0O__Format : rA_Report_r16__ext0O__Type t_Format

val rA_Report_r16__ext0__check_all_none : rA_Report_r16__ext0O__Type -> bool

val rA_Report_r16__ext0__Format : rA_Report_r16__ext0__Type t_Format

type rA_Report_r16__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val rA_Report_r16__root_Format_list : rA_Report_r16__root_Format_Type

type rA_Report_r16__ext_Format_Type =
  rA_Report_r16__ext0__Type t_Format * unit t_Format

val rA_Report_r16__ext_Format_list : rA_Report_r16__ext_Format_Type

type rA_Report_r16__list_type = seq_type * seq_ext_type

val rA_Report_r16__list_format : rA_Report_r16__list_type t_Format

val rA_Report_r16__F1 : rA_Report_r16__Type -> rA_Report_r16__list_type

val rA_Report_r16__F2 : rA_Report_r16__list_type -> rA_Report_r16__Type

val rA_Report_r16__Format : rA_Report_r16__Type t_Format

type rA_ReportList_r16__Type = rA_Report_r16__Type list

val rA_ReportList_r16__Format : rA_ReportList_r16__Type t_Format

type measResultRLFNR_r16__measResult_r16__cellResults_r16__Type = { measResultRLFNR_r16__measResult_r16__cellResults_r16__resultsSSB_Cell_r16 : 
                                                                    measQuantityResults__Type
                                                                    option;
                                                                    measResultRLFNR_r16__measResult_r16__cellResults_r16__resultsCSI_RS_Cell_r16 : 
                                                                    measQuantityResults__Type
                                                                    option }

val measResultRLFNR_r16__measResult_r16__cellResults_r16__list : seq_elem list

type measResultRLFNR_r16__measResult_r16__rsIndexResults_r16__ssbRLMConfigBitmap_r16__Type =
  bit_string_fixed

type measResultRLFNR_r16__measResult_r16__rsIndexResults_r16__csi_rsRLMConfigBitmap_r16__Type =
  bit_string_fixed

type measResultRLFNR_r16__measResult_r16__rsIndexResults_r16__Type = { 
measResultRLFNR_r16__measResult_r16__rsIndexResults_r16__resultsSSB_Indexes_r16 : 
resultsPerSSB_IndexList__Type option;
measResultRLFNR_r16__measResult_r16__rsIndexResults_r16__ssbRLMConfigBitmap_r16 : 
measResultRLFNR_r16__measResult_r16__rsIndexResults_r16__ssbRLMConfigBitmap_r16__Type
option;
measResultRLFNR_r16__measResult_r16__rsIndexResults_r16__resultsCSI_RS_Indexes_r16 : 
resultsPerCSI_RS_IndexList__Type option;
measResultRLFNR_r16__measResult_r16__rsIndexResults_r16__csi_rsRLMConfigBitmap_r16 : 
measResultRLFNR_r16__measResult_r16__rsIndexResults_r16__csi_rsRLMConfigBitmap_r16__Type
option }

val measResultRLFNR_r16__measResult_r16__rsIndexResults_r16__list :
  seq_elem list

type measResultRLFNR_r16__measResult_r16__Type = { measResultRLFNR_r16__measResult_r16__cellResults_r16 : 
                                                   measResultRLFNR_r16__measResult_r16__cellResults_r16__Type;
                                                   measResultRLFNR_r16__measResult_r16__rsIndexResults_r16 : 
                                                   measResultRLFNR_r16__measResult_r16__rsIndexResults_r16__Type
                                                   option }

val measResultRLFNR_r16__measResult_r16__list : seq_elem list

type measResultRLFNR_r16__Type = { measResultRLFNR_r16__measResult_r16 : 
                                   measResultRLFNR_r16__measResult_r16__Type }

val measResultRLFNR_r16__list : seq_elem list

type measResultRLFNR_r16__measResult_r16__cellResults_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val measResultRLFNR_r16__measResult_r16__cellResults_r16__Format_list :
  measResultRLFNR_r16__measResult_r16__cellResults_r16__Format_Type

val measResultRLFNR_r16__measResult_r16__cellResults_r16__list__Format :
  seq_type t_Format

val measResultRLFNR_r16__measResult_r16__cellResults_r16__F1 :
  measResultRLFNR_r16__measResult_r16__cellResults_r16__Type ->
  measQuantityResults__Type option * (measQuantityResults__Type option * unit)

val measResultRLFNR_r16__measResult_r16__cellResults_r16__F2 :
  seq_type -> measResultRLFNR_r16__measResult_r16__cellResults_r16__Type

val measResultRLFNR_r16__measResult_r16__cellResults_r16__Format :
  measResultRLFNR_r16__measResult_r16__cellResults_r16__Type t_Format

val measResultRLFNR_r16__measResult_r16__rsIndexResults_r16__ssbRLMConfigBitmap_r16__Format :
  measResultRLFNR_r16__measResult_r16__rsIndexResults_r16__ssbRLMConfigBitmap_r16__Type
  t_Format

val measResultRLFNR_r16__measResult_r16__rsIndexResults_r16__csi_rsRLMConfigBitmap_r16__Format :
  measResultRLFNR_r16__measResult_r16__rsIndexResults_r16__csi_rsRLMConfigBitmap_r16__Type
  t_Format

type measResultRLFNR_r16__measResult_r16__rsIndexResults_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

val measResultRLFNR_r16__measResult_r16__rsIndexResults_r16__Format_list :
  measResultRLFNR_r16__measResult_r16__rsIndexResults_r16__Format_Type

val measResultRLFNR_r16__measResult_r16__rsIndexResults_r16__list__Format :
  seq_type t_Format

val measResultRLFNR_r16__measResult_r16__rsIndexResults_r16__F1 :
  measResultRLFNR_r16__measResult_r16__rsIndexResults_r16__Type ->
  resultsPerSSB_IndexList__Type
  option * (measResultRLFNR_r16__measResult_r16__rsIndexResults_r16__ssbRLMConfigBitmap_r16__Type
  option * (resultsPerCSI_RS_IndexList__Type
  option * (measResultRLFNR_r16__measResult_r16__rsIndexResults_r16__csi_rsRLMConfigBitmap_r16__Type
  option * unit)))

val measResultRLFNR_r16__measResult_r16__rsIndexResults_r16__F2 :
  seq_type -> measResultRLFNR_r16__measResult_r16__rsIndexResults_r16__Type

val measResultRLFNR_r16__measResult_r16__rsIndexResults_r16__Format :
  measResultRLFNR_r16__measResult_r16__rsIndexResults_r16__Type t_Format

type measResultRLFNR_r16__measResult_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val measResultRLFNR_r16__measResult_r16__Format_list :
  measResultRLFNR_r16__measResult_r16__Format_Type

val measResultRLFNR_r16__measResult_r16__list__Format : seq_type t_Format

val measResultRLFNR_r16__measResult_r16__F1 :
  measResultRLFNR_r16__measResult_r16__Type ->
  measResultRLFNR_r16__measResult_r16__cellResults_r16__Type * (measResultRLFNR_r16__measResult_r16__rsIndexResults_r16__Type
  option * unit)

val measResultRLFNR_r16__measResult_r16__F2 :
  seq_type -> measResultRLFNR_r16__measResult_r16__Type

val measResultRLFNR_r16__measResult_r16__Format :
  measResultRLFNR_r16__measResult_r16__Type t_Format

type measResultRLFNR_r16__Format_Type = seq_elem_to_format * seq_elem_to_format

val measResultRLFNR_r16__Format_list : measResultRLFNR_r16__Format_Type

val measResultRLFNR_r16__list__Format : seq_type t_Format

val measResultRLFNR_r16__F1 :
  measResultRLFNR_r16__Type -> measResultRLFNR_r16__measResult_r16__Type * unit

val measResultRLFNR_r16__F2 : seq_type -> measResultRLFNR_r16__Type

val measResultRLFNR_r16__Format : measResultRLFNR_r16__Type t_Format

type rNTI_Value__Type = int

val rNTI_Value__Format : int t_Format

type cGI_InfoEUTRALogging__cellIdentity_eutra_5gc__Type = bit_string_fixed

type cGI_InfoEUTRALogging__trackingAreaCode_eutra_epc__Type = bit_string_fixed

type cGI_InfoEUTRALogging__cellIdentity_eutra_epc__Type = bit_string_fixed

type cGI_InfoEUTRALogging__Type = { cGI_InfoEUTRALogging__plmn_Identity_eutra_5gc : 
                                    pLMN_Identity__Type option;
                                    cGI_InfoEUTRALogging__trackingAreaCode_eutra_5gc : 
                                    trackingAreaCode__Type option;
                                    cGI_InfoEUTRALogging__cellIdentity_eutra_5gc : 
                                    cGI_InfoEUTRALogging__cellIdentity_eutra_5gc__Type
                                    option;
                                    cGI_InfoEUTRALogging__plmn_Identity_eutra_epc : 
                                    pLMN_Identity__Type option;
                                    cGI_InfoEUTRALogging__trackingAreaCode_eutra_epc : 
                                    cGI_InfoEUTRALogging__trackingAreaCode_eutra_epc__Type
                                    option;
                                    cGI_InfoEUTRALogging__cellIdentity_eutra_epc : 
                                    cGI_InfoEUTRALogging__cellIdentity_eutra_epc__Type
                                    option }

val cGI_InfoEUTRALogging__list : seq_elem list

val cGI_InfoEUTRALogging__cellIdentity_eutra_5gc__Format :
  cGI_InfoEUTRALogging__cellIdentity_eutra_5gc__Type t_Format

val cGI_InfoEUTRALogging__trackingAreaCode_eutra_epc__Format :
  cGI_InfoEUTRALogging__trackingAreaCode_eutra_epc__Type t_Format

val cGI_InfoEUTRALogging__cellIdentity_eutra_epc__Format :
  cGI_InfoEUTRALogging__cellIdentity_eutra_epc__Type t_Format

type cGI_InfoEUTRALogging__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))))

val cGI_InfoEUTRALogging__Format_list : cGI_InfoEUTRALogging__Format_Type

val cGI_InfoEUTRALogging__list__Format : seq_type t_Format

val cGI_InfoEUTRALogging__F1 :
  cGI_InfoEUTRALogging__Type -> pLMN_Identity__Type
  option * (trackingAreaCode__Type
  option * (cGI_InfoEUTRALogging__cellIdentity_eutra_5gc__Type
  option * (pLMN_Identity__Type
  option * (cGI_InfoEUTRALogging__trackingAreaCode_eutra_epc__Type
  option * (cGI_InfoEUTRALogging__cellIdentity_eutra_epc__Type
  option * unit)))))

val cGI_InfoEUTRALogging__F2 : seq_type -> cGI_InfoEUTRALogging__Type

val cGI_InfoEUTRALogging__Format : cGI_InfoEUTRALogging__Type t_Format

type pCI_ARFCN_EUTRA_r16__Type = { pCI_ARFCN_EUTRA_r16__physCellId_r16 : 
                                   eUTRA_PhysCellId__Type;
                                   pCI_ARFCN_EUTRA_r16__carrierFreq_r16 : 
                                   aRFCN_ValueEUTRA__Type }

val pCI_ARFCN_EUTRA_r16__list : seq_elem list

type pCI_ARFCN_EUTRA_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val pCI_ARFCN_EUTRA_r16__Format_list : pCI_ARFCN_EUTRA_r16__Format_Type

val pCI_ARFCN_EUTRA_r16__list__Format : seq_type t_Format

val pCI_ARFCN_EUTRA_r16__F1 :
  pCI_ARFCN_EUTRA_r16__Type ->
  eUTRA_PhysCellId__Type * (aRFCN_ValueEUTRA__Type * unit)

val pCI_ARFCN_EUTRA_r16__F2 : seq_type -> pCI_ARFCN_EUTRA_r16__Type

val pCI_ARFCN_EUTRA_r16__Format : pCI_ARFCN_EUTRA_r16__Type t_Format

type timeUntilReconnection_r16__Type = int

val timeUntilReconnection_r16__Format : int t_Format

type timeConnSourceDAPS_Failure_r17__Type = int

val timeConnSourceDAPS_Failure_r17__Format : int t_Format

type timeSinceCHO_Reconfig_r17__Type = int

val timeSinceCHO_Reconfig_r17__Format : int t_Format

type choCandidateCell_r17__Type =
| ChoCandidateCell_r17__cellGlobalId_r17 of cGI_Info_Logging_r16__Type
| ChoCandidateCell_r17__pci_arfcn_r17 of pCI_ARFCN_NR_r16__Type

val choCandidateCell_r17__list__Format : (int, __) sigT t_Format

val choCandidateCell_r17__F1 : choCandidateCell_r17__Type -> choice

val choCandidateCell_r17__F2 : choice -> choCandidateCell_r17__Type

val choCandidateCell_r17__Format : choCandidateCell_r17__Type t_Format

type choCandidateCellList_r17__Type = choCandidateCell_r17__Type list

val choCandidateCellList_r17__Format : choCandidateCellList_r17__Type t_Format

type rLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__Type = { 
rLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__measResultListNR_r16 : 
measResultList2NR_r16__Type option;
rLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__measResultListEUTRA_r16 : 
measResultList2EUTRA_r16__Type option }

val rLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__list :
  seq_elem list

type rLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__Type =
| RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__nrPreviousCell_r16 of 
   cGI_Info_Logging_r16__Type
| RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__eutraPreviousCell_r16 of 
   cGI_InfoEUTRALogging__Type

type rLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__Type =
| RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__cellGlobalId_r16 of 
   cGI_Info_Logging_r16__Type
| RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__pci_arfcn_r16 of 
   pCI_ARFCN_NR_r16__Type

type rLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__Type =
| RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__cellGlobalId_r16 of 
   cGI_InfoEUTRALogging__Type
| RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__pci_arfcn_r16 of 
   pCI_ARFCN_EUTRA_r16__Type

type rLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__Type =
| RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16 of 
   rLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__Type
| RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16 of 
   rLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__Type

type rLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__Type =
| RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__nrReconnectCellId_r16 of 
   cGI_Info_Logging_r16__Type
| RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__eutraReconnectCellId_r16 of 
   cGI_InfoEUTRALogging__Type

type rLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__Type =
| RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__rlf
| RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__hof

val rLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__nat__Format :
  int t_Format

val rLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__F1 :
  rLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__Type -> int

val rLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__F2 :
  int -> rLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__Type

type rLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__Type =
| RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__t310_Expiry
| RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__randomAccessProblem
| RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__rlc_MaxNumRetx
| RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__beamFailureRecoveryFailure
| RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__lbtFailure_r16
| RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__bh_rlfRecoveryFailure
| RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__t312_expiry_r17
| RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__spare1

val rLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__nat__Format :
  int t_Format

val rLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__F1 :
  rLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__Type -> int

val rLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__F2 :
  int -> rLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__Type

type rLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__Type =
| RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__true

val rLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__nat__Format :
  int t_Format

val rLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__F1 :
  rLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__Type -> int

val rLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__F2 :
  int -> rLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__Type

type rLF_Report_r16__nr_RLF_Report_r16__ext0O__csi_rsRLMConfigBitmap_v1650__Type =
  bit_string_fixed

type rLF_Report_r16__nr_RLF_Report_r16__ext0O__Type = { rLF_Report_r16__nr_RLF_Report_r16__ext0O__csi_rsRLMConfigBitmap_v1650 : 
                                                        rLF_Report_r16__nr_RLF_Report_r16__ext0O__csi_rsRLMConfigBitmap_v1650__Type
                                                        option }

val rLF_Report_r16__nr_RLF_Report_r16__ext0O__list : seq_elem list

type rLF_Report_r16__nr_RLF_Report_r16__ext0__Type =
  rLF_Report_r16__nr_RLF_Report_r16__ext0O__Type

type rLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__Type =
| RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__cho
| RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__daps
| RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__spare2
| RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__spare1

val rLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__nat__Format :
  int t_Format

val rLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__F1 :
  rLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__Type -> int

val rLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__F2 :
  int -> rLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__Type

type rLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__Type =
| RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__cellGlobalId_r17 of 
   cGI_Info_Logging_r16__Type
| RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__pci_arfcn_r17 of 
   pCI_ARFCN_NR_r16__Type

type rLF_Report_r16__nr_RLF_Report_r16__ext1O__Type = { rLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17 : 
                                                        rLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__Type
                                                        option;
                                                        rLF_Report_r16__nr_RLF_Report_r16__ext1O__timeConnSourceDAPS_Failure_r17 : 
                                                        timeConnSourceDAPS_Failure_r17__Type
                                                        option;
                                                        rLF_Report_r16__nr_RLF_Report_r16__ext1O__timeSinceCHO_Reconfig_r17 : 
                                                        timeSinceCHO_Reconfig_r17__Type
                                                        option;
                                                        rLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17 : 
                                                        rLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__Type
                                                        option;
                                                        rLF_Report_r16__nr_RLF_Report_r16__ext1O__choCandidateCellList_r17 : 
                                                        choCandidateCellList_r17__Type
                                                        option }

val rLF_Report_r16__nr_RLF_Report_r16__ext1O__list : seq_elem list

type rLF_Report_r16__nr_RLF_Report_r16__ext1__Type =
  rLF_Report_r16__nr_RLF_Report_r16__ext1O__Type

type rLF_Report_r16__nr_RLF_Report_r16__Type = { rLF_Report_r16__nr_RLF_Report_r16__measResultLastServCell_r16 : 
                                                 measResultRLFNR_r16__Type;
                                                 rLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16 : 
                                                 rLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__Type
                                                 option;
                                                 rLF_Report_r16__nr_RLF_Report_r16__c_RNTI_r16 : 
                                                 rNTI_Value__Type;
                                                 rLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16 : 
                                                 rLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__Type
                                                 option;
                                                 rLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16 : 
                                                 rLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__Type;
                                                 rLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16 : 
                                                 rLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__Type
                                                 option;
                                                 rLF_Report_r16__nr_RLF_Report_r16__timeUntilReconnection_r16 : 
                                                 timeUntilReconnection_r16__Type
                                                 option;
                                                 rLF_Report_r16__nr_RLF_Report_r16__reestablishmentCellId_r16 : 
                                                 cGI_Info_Logging_r16__Type
                                                 option;
                                                 rLF_Report_r16__nr_RLF_Report_r16__timeConnFailure_r16 : 
                                                 int option;
                                                 rLF_Report_r16__nr_RLF_Report_r16__timeSinceFailure_r16 : 
                                                 timeSinceFailure_r16__Type;
                                                 rLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16 : 
                                                 rLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__Type;
                                                 rLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16 : 
                                                 rLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__Type;
                                                 rLF_Report_r16__nr_RLF_Report_r16__locationInfo_r16 : 
                                                 locationInfo_r16__Type option;
                                                 rLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16 : 
                                                 rLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__Type
                                                 option;
                                                 rLF_Report_r16__nr_RLF_Report_r16__ra_InformationCommon_r16 : 
                                                 rA_InformationCommon_r16__Type
                                                 option;
                                                 rLF_Report_r16__nr_RLF_Report_r16__ext0 : 
                                                 rLF_Report_r16__nr_RLF_Report_r16__ext0__Type
                                                 option;
                                                 rLF_Report_r16__nr_RLF_Report_r16__ext1 : 
                                                 rLF_Report_r16__nr_RLF_Report_r16__ext1__Type
                                                 option }

val rLF_Report_r16__nr_RLF_Report_r16__root_list : seq_elem list

val rLF_Report_r16__nr_RLF_Report_r16__ext_list : typ list

type rLF_Report_r16__eutra_RLF_Report_r16__ext0O__Type = { rLF_Report_r16__eutra_RLF_Report_r16__ext0O__measResult_RLF_Report_EUTRA_v1690 : 
                                                           octet_string option }

val rLF_Report_r16__eutra_RLF_Report_r16__ext0O__list : seq_elem list

type rLF_Report_r16__eutra_RLF_Report_r16__ext0__Type =
  rLF_Report_r16__eutra_RLF_Report_r16__ext0O__Type

type rLF_Report_r16__eutra_RLF_Report_r16__Type = { rLF_Report_r16__eutra_RLF_Report_r16__failedPCellId_EUTRA : 
                                                    cGI_InfoEUTRALogging__Type;
                                                    rLF_Report_r16__eutra_RLF_Report_r16__measResult_RLF_Report_EUTRA_r16 : 
                                                    octet_string;
                                                    rLF_Report_r16__eutra_RLF_Report_r16__ext0 : 
                                                    rLF_Report_r16__eutra_RLF_Report_r16__ext0__Type
                                                    option }

val rLF_Report_r16__eutra_RLF_Report_r16__root_list : seq_elem list

val rLF_Report_r16__eutra_RLF_Report_r16__ext_list : typ list

type rLF_Report_r16__Type =
| RLF_Report_r16__nr_RLF_Report_r16 of rLF_Report_r16__nr_RLF_Report_r16__Type
| RLF_Report_r16__eutra_RLF_Report_r16 of rLF_Report_r16__eutra_RLF_Report_r16__Type

type rLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val rLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__Format_list :
  rLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__Format_Type

val rLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__list__Format :
  seq_type t_Format

val rLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__F1 :
  rLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__Type ->
  measResultList2NR_r16__Type option * (measResultList2EUTRA_r16__Type
  option * unit)

val rLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__F2 :
  seq_type -> rLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__Type

val rLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__Format :
  rLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__Type t_Format

val rLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__list__Format :
  (int, __) sigT t_Format

val rLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__F1 :
  rLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__Type -> choice

val rLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__F2 :
  choice -> rLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__Type

val rLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__Format :
  rLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__Type t_Format

val rLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__list__Format :
  (int, __) sigT t_Format

val rLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__F1 :
  rLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__Type
  -> choice

val rLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__F2 :
  choice ->
  rLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__Type

val rLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__Format :
  rLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__Type
  t_Format

val rLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__list__Format :
  (int, __) sigT t_Format

val rLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__F1 :
  rLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__Type
  -> choice

val rLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__F2 :
  choice ->
  rLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__Type

val rLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__Format :
  rLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__Type
  t_Format

val rLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__list__Format :
  (int, __) sigT t_Format

val rLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__F1 :
  rLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__Type -> choice

val rLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__F2 :
  choice -> rLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__Type

val rLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__Format :
  rLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__Type t_Format

val rLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__list__Format :
  (int, __) sigT t_Format

val rLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__F1 :
  rLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__Type -> choice

val rLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__F2 :
  choice -> rLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__Type

val rLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__Format :
  rLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__Type t_Format

val rLF_Report_r16__nr_RLF_Report_r16__timeConnFailure_r16__Format :
  int t_Format

val rLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__Format :
  rLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__Type t_Format

val rLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__Format :
  rLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__Type t_Format

val rLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__Format :
  rLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__Type t_Format

val rLF_Report_r16__nr_RLF_Report_r16__ext0O__csi_rsRLMConfigBitmap_v1650__Format :
  rLF_Report_r16__nr_RLF_Report_r16__ext0O__csi_rsRLMConfigBitmap_v1650__Type
  t_Format

type rLF_Report_r16__nr_RLF_Report_r16__ext0O__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val rLF_Report_r16__nr_RLF_Report_r16__ext0O__Format_list :
  rLF_Report_r16__nr_RLF_Report_r16__ext0O__Format_Type

val rLF_Report_r16__nr_RLF_Report_r16__ext0O__list__Format : seq_type t_Format

val rLF_Report_r16__nr_RLF_Report_r16__ext0O__F1 :
  rLF_Report_r16__nr_RLF_Report_r16__ext0O__Type ->
  rLF_Report_r16__nr_RLF_Report_r16__ext0O__csi_rsRLMConfigBitmap_v1650__Type
  option * unit

val rLF_Report_r16__nr_RLF_Report_r16__ext0O__F2 :
  seq_type -> rLF_Report_r16__nr_RLF_Report_r16__ext0O__Type

val rLF_Report_r16__nr_RLF_Report_r16__ext0O__Format :
  rLF_Report_r16__nr_RLF_Report_r16__ext0O__Type t_Format

val rLF_Report_r16__nr_RLF_Report_r16__ext0__check_all_none :
  rLF_Report_r16__nr_RLF_Report_r16__ext0O__Type -> bool

val rLF_Report_r16__nr_RLF_Report_r16__ext0__Format :
  rLF_Report_r16__nr_RLF_Report_r16__ext0__Type t_Format

val rLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__Format :
  rLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__Type t_Format

val rLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__list__Format :
  (int, __) sigT t_Format

val rLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__F1 :
  rLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__Type -> choice

val rLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__F2 :
  choice -> rLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__Type

val rLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__Format :
  rLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__Type t_Format

type rLF_Report_r16__nr_RLF_Report_r16__ext1O__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))))

val rLF_Report_r16__nr_RLF_Report_r16__ext1O__Format_list :
  rLF_Report_r16__nr_RLF_Report_r16__ext1O__Format_Type

val rLF_Report_r16__nr_RLF_Report_r16__ext1O__list__Format : seq_type t_Format

val rLF_Report_r16__nr_RLF_Report_r16__ext1O__F1 :
  rLF_Report_r16__nr_RLF_Report_r16__ext1O__Type ->
  rLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__Type
  option * (timeConnSourceDAPS_Failure_r17__Type
  option * (timeSinceCHO_Reconfig_r17__Type
  option * (rLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__Type
  option * (choCandidateCellList_r17__Type option * unit))))

val rLF_Report_r16__nr_RLF_Report_r16__ext1O__F2 :
  seq_type -> rLF_Report_r16__nr_RLF_Report_r16__ext1O__Type

val rLF_Report_r16__nr_RLF_Report_r16__ext1O__Format :
  rLF_Report_r16__nr_RLF_Report_r16__ext1O__Type t_Format

val rLF_Report_r16__nr_RLF_Report_r16__ext1__check_all_none :
  rLF_Report_r16__nr_RLF_Report_r16__ext1O__Type -> bool

val rLF_Report_r16__nr_RLF_Report_r16__ext1__Format :
  rLF_Report_r16__nr_RLF_Report_r16__ext1__Type t_Format

type rLF_Report_r16__nr_RLF_Report_r16__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))))))))))))))

val rLF_Report_r16__nr_RLF_Report_r16__root_Format_list :
  rLF_Report_r16__nr_RLF_Report_r16__root_Format_Type

type rLF_Report_r16__nr_RLF_Report_r16__ext_Format_Type =
  rLF_Report_r16__nr_RLF_Report_r16__ext0__Type
  t_Format * (rLF_Report_r16__nr_RLF_Report_r16__ext1__Type t_Format * unit
  t_Format)

val rLF_Report_r16__nr_RLF_Report_r16__ext_Format_list :
  rLF_Report_r16__nr_RLF_Report_r16__ext_Format_Type

type rLF_Report_r16__nr_RLF_Report_r16__list_type = seq_type * seq_ext_type

val rLF_Report_r16__nr_RLF_Report_r16__list_format :
  rLF_Report_r16__nr_RLF_Report_r16__list_type t_Format

val rLF_Report_r16__nr_RLF_Report_r16__F1 :
  rLF_Report_r16__nr_RLF_Report_r16__Type ->
  rLF_Report_r16__nr_RLF_Report_r16__list_type

val rLF_Report_r16__nr_RLF_Report_r16__F2 :
  rLF_Report_r16__nr_RLF_Report_r16__list_type ->
  rLF_Report_r16__nr_RLF_Report_r16__Type

val rLF_Report_r16__nr_RLF_Report_r16__Format :
  rLF_Report_r16__nr_RLF_Report_r16__Type t_Format

type rLF_Report_r16__eutra_RLF_Report_r16__ext0O__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val rLF_Report_r16__eutra_RLF_Report_r16__ext0O__Format_list :
  rLF_Report_r16__eutra_RLF_Report_r16__ext0O__Format_Type

val rLF_Report_r16__eutra_RLF_Report_r16__ext0O__list__Format :
  seq_type t_Format

val rLF_Report_r16__eutra_RLF_Report_r16__ext0O__F1 :
  rLF_Report_r16__eutra_RLF_Report_r16__ext0O__Type -> octet_string
  option * unit

val rLF_Report_r16__eutra_RLF_Report_r16__ext0O__F2 :
  seq_type -> rLF_Report_r16__eutra_RLF_Report_r16__ext0O__Type

val rLF_Report_r16__eutra_RLF_Report_r16__ext0O__Format :
  rLF_Report_r16__eutra_RLF_Report_r16__ext0O__Type t_Format

val rLF_Report_r16__eutra_RLF_Report_r16__ext0__check_all_none :
  rLF_Report_r16__eutra_RLF_Report_r16__ext0O__Type -> bool

val rLF_Report_r16__eutra_RLF_Report_r16__ext0__Format :
  rLF_Report_r16__eutra_RLF_Report_r16__ext0__Type t_Format

type rLF_Report_r16__eutra_RLF_Report_r16__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val rLF_Report_r16__eutra_RLF_Report_r16__root_Format_list :
  rLF_Report_r16__eutra_RLF_Report_r16__root_Format_Type

type rLF_Report_r16__eutra_RLF_Report_r16__ext_Format_Type =
  rLF_Report_r16__eutra_RLF_Report_r16__ext0__Type t_Format * unit t_Format

val rLF_Report_r16__eutra_RLF_Report_r16__ext_Format_list :
  rLF_Report_r16__eutra_RLF_Report_r16__ext_Format_Type

type rLF_Report_r16__eutra_RLF_Report_r16__list_type = seq_type * seq_ext_type

val rLF_Report_r16__eutra_RLF_Report_r16__list_format :
  rLF_Report_r16__eutra_RLF_Report_r16__list_type t_Format

val rLF_Report_r16__eutra_RLF_Report_r16__F1 :
  rLF_Report_r16__eutra_RLF_Report_r16__Type ->
  rLF_Report_r16__eutra_RLF_Report_r16__list_type

val rLF_Report_r16__eutra_RLF_Report_r16__F2 :
  rLF_Report_r16__eutra_RLF_Report_r16__list_type ->
  rLF_Report_r16__eutra_RLF_Report_r16__Type

val rLF_Report_r16__eutra_RLF_Report_r16__Format :
  rLF_Report_r16__eutra_RLF_Report_r16__Type t_Format

val rLF_Report_r16__list__Format : (int, __) sigT t_Format

val rLF_Report_r16__F1 : rLF_Report_r16__Type -> choice

val rLF_Report_r16__F2 : choice -> rLF_Report_r16__Type

val rLF_Report_r16__Format : rLF_Report_r16__Type t_Format

type visitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__Type =
| VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__cgi_Info_r17 of 
   cGI_Info_Logging_r16__Type
| VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__pci_arfcn_r17 of 
   pCI_ARFCN_NR_r16__Type

type visitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__Type =
| VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__cellGlobalId_r17 of 
   cGI_InfoEUTRALogging__Type
| VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__pci_arfcn_r17 of 
   pCI_ARFCN_EUTRA_r16__Type

type visitedPSCellInfo_r17__visitedCellId_r17__Type =
| VisitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17 of visitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__Type
| VisitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17 of visitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__Type

type visitedPSCellInfo_r17__Type = { visitedPSCellInfo_r17__visitedCellId_r17 : 
                                     visitedPSCellInfo_r17__visitedCellId_r17__Type
                                     option;
                                     visitedPSCellInfo_r17__timeSpent_r17 : 
                                     int }

val visitedPSCellInfo_r17__root_list : seq_elem list

val visitedPSCellInfo_r17__ext_list : typ list

val visitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__list__Format :
  (int, __) sigT t_Format

val visitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__F1 :
  visitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__Type -> choice

val visitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__F2 :
  choice -> visitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__Type

val visitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__Format :
  visitedPSCellInfo_r17__visitedCellId_r17__nr_CellId_r17__Type t_Format

val visitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__list__Format :
  (int, __) sigT t_Format

val visitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__F1 :
  visitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__Type -> choice

val visitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__F2 :
  choice -> visitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__Type

val visitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__Format :
  visitedPSCellInfo_r17__visitedCellId_r17__eutra_CellId_r17__Type t_Format

val visitedPSCellInfo_r17__visitedCellId_r17__list__Format :
  (int, __) sigT t_Format

val visitedPSCellInfo_r17__visitedCellId_r17__F1 :
  visitedPSCellInfo_r17__visitedCellId_r17__Type -> choice

val visitedPSCellInfo_r17__visitedCellId_r17__F2 :
  choice -> visitedPSCellInfo_r17__visitedCellId_r17__Type

val visitedPSCellInfo_r17__visitedCellId_r17__Format :
  visitedPSCellInfo_r17__visitedCellId_r17__Type t_Format

val visitedPSCellInfo_r17__timeSpent_r17__Format : int t_Format

type visitedPSCellInfo_r17__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val visitedPSCellInfo_r17__root_Format_list :
  visitedPSCellInfo_r17__root_Format_Type

type visitedPSCellInfo_r17__ext_Format_Type = unit t_Format

val visitedPSCellInfo_r17__ext_Format_list :
  visitedPSCellInfo_r17__ext_Format_Type

type visitedPSCellInfo_r17__list_type = seq_type * seq_ext_type

val visitedPSCellInfo_r17__list_format :
  visitedPSCellInfo_r17__list_type t_Format

val visitedPSCellInfo_r17__F1 :
  visitedPSCellInfo_r17__Type -> visitedPSCellInfo_r17__list_type

val visitedPSCellInfo_r17__F2 :
  visitedPSCellInfo_r17__list_type -> visitedPSCellInfo_r17__Type

val visitedPSCellInfo_r17__Format : visitedPSCellInfo_r17__Type t_Format

type visitedPSCellInfoList_r17__Type = visitedPSCellInfo_r17__Type list

val visitedPSCellInfoList_r17__Format :
  visitedPSCellInfoList_r17__Type t_Format

type visitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__Type =
| VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__cgi_Info of cGI_Info_Logging_r16__Type
| VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__pci_arfcn_r16 of 
   pCI_ARFCN_NR_r16__Type

type visitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__Type =
| VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__cellGlobalId_r16 of 
   cGI_InfoEUTRA__Type
| VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__pci_arfcn_r16 of 
   pCI_ARFCN_EUTRA_r16__Type

type visitedCellInfo_r16__visitedCellId_r16__Type =
| VisitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16 of visitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__Type
| VisitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16 of visitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__Type

type visitedCellInfo_r16__ext0O__Type = { visitedCellInfo_r16__ext0O__visitedPSCellInfoListReport_r17 : 
                                          visitedPSCellInfoList_r17__Type
                                          option }

val visitedCellInfo_r16__ext0O__list : seq_elem list

type visitedCellInfo_r16__ext0__Type = visitedCellInfo_r16__ext0O__Type

type visitedCellInfo_r16__Type = { visitedCellInfo_r16__visitedCellId_r16 : 
                                   visitedCellInfo_r16__visitedCellId_r16__Type
                                   option;
                                   visitedCellInfo_r16__timeSpent_r16 : 
                                   int;
                                   visitedCellInfo_r16__ext0 : visitedCellInfo_r16__ext0__Type
                                                               option }

val visitedCellInfo_r16__root_list : seq_elem list

val visitedCellInfo_r16__ext_list : typ list

val visitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__list__Format :
  (int, __) sigT t_Format

val visitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__F1 :
  visitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__Type -> choice

val visitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__F2 :
  choice -> visitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__Type

val visitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__Format :
  visitedCellInfo_r16__visitedCellId_r16__nr_CellId_r16__Type t_Format

val visitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__list__Format :
  (int, __) sigT t_Format

val visitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__F1 :
  visitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__Type -> choice

val visitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__F2 :
  choice -> visitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__Type

val visitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__Format :
  visitedCellInfo_r16__visitedCellId_r16__eutra_CellId_r16__Type t_Format

val visitedCellInfo_r16__visitedCellId_r16__list__Format :
  (int, __) sigT t_Format

val visitedCellInfo_r16__visitedCellId_r16__F1 :
  visitedCellInfo_r16__visitedCellId_r16__Type -> choice

val visitedCellInfo_r16__visitedCellId_r16__F2 :
  choice -> visitedCellInfo_r16__visitedCellId_r16__Type

val visitedCellInfo_r16__visitedCellId_r16__Format :
  visitedCellInfo_r16__visitedCellId_r16__Type t_Format

val visitedCellInfo_r16__timeSpent_r16__Format : int t_Format

type visitedCellInfo_r16__ext0O__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val visitedCellInfo_r16__ext0O__Format_list :
  visitedCellInfo_r16__ext0O__Format_Type

val visitedCellInfo_r16__ext0O__list__Format : seq_type t_Format

val visitedCellInfo_r16__ext0O__F1 :
  visitedCellInfo_r16__ext0O__Type -> visitedPSCellInfoList_r17__Type
  option * unit

val visitedCellInfo_r16__ext0O__F2 :
  seq_type -> visitedCellInfo_r16__ext0O__Type

val visitedCellInfo_r16__ext0O__Format :
  visitedCellInfo_r16__ext0O__Type t_Format

val visitedCellInfo_r16__ext0__check_all_none :
  visitedCellInfo_r16__ext0O__Type -> bool

val visitedCellInfo_r16__ext0__Format :
  visitedCellInfo_r16__ext0__Type t_Format

type visitedCellInfo_r16__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val visitedCellInfo_r16__root_Format_list :
  visitedCellInfo_r16__root_Format_Type

type visitedCellInfo_r16__ext_Format_Type =
  visitedCellInfo_r16__ext0__Type t_Format * unit t_Format

val visitedCellInfo_r16__ext_Format_list : visitedCellInfo_r16__ext_Format_Type

type visitedCellInfo_r16__list_type = seq_type * seq_ext_type

val visitedCellInfo_r16__list_format : visitedCellInfo_r16__list_type t_Format

val visitedCellInfo_r16__F1 :
  visitedCellInfo_r16__Type -> visitedCellInfo_r16__list_type

val visitedCellInfo_r16__F2 :
  visitedCellInfo_r16__list_type -> visitedCellInfo_r16__Type

val visitedCellInfo_r16__Format : visitedCellInfo_r16__Type t_Format

type visitedCellInfoList_r16__Type = visitedCellInfo_r16__Type list

val visitedCellInfoList_r16__Format : visitedCellInfoList_r16__Type t_Format

type mobilityHistoryReport_r16__Type = visitedCellInfoList_r16__Type

val mobilityHistoryReport_r16__Format : visitedCellInfoList_r16__Type t_Format

type measResultSuccessHONR_r17__measResult_r17__cellResults_r17__Type = { 
measResultSuccessHONR_r17__measResult_r17__cellResults_r17__resultsSSB_Cell_r17 : 
measQuantityResults__Type option;
measResultSuccessHONR_r17__measResult_r17__cellResults_r17__resultsCSI_RS_Cell_r17 : 
measQuantityResults__Type option }

val measResultSuccessHONR_r17__measResult_r17__cellResults_r17__list :
  seq_elem list

type measResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__Type = { 
measResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__resultsSSB_Indexes_r17 : 
resultsPerSSB_IndexList__Type option;
measResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__resultsCSI_RS_Indexes_r17 : 
resultsPerCSI_RS_IndexList__Type option }

val measResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__list :
  seq_elem list

type measResultSuccessHONR_r17__measResult_r17__Type = { measResultSuccessHONR_r17__measResult_r17__cellResults_r17 : 
                                                         measResultSuccessHONR_r17__measResult_r17__cellResults_r17__Type;
                                                         measResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17 : 
                                                         measResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__Type }

val measResultSuccessHONR_r17__measResult_r17__list : seq_elem list

type measResultSuccessHONR_r17__Type = { measResultSuccessHONR_r17__measResult_r17 : 
                                         measResultSuccessHONR_r17__measResult_r17__Type }

val measResultSuccessHONR_r17__list : seq_elem list

type measResultSuccessHONR_r17__measResult_r17__cellResults_r17__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val measResultSuccessHONR_r17__measResult_r17__cellResults_r17__Format_list :
  measResultSuccessHONR_r17__measResult_r17__cellResults_r17__Format_Type

val measResultSuccessHONR_r17__measResult_r17__cellResults_r17__list__Format :
  seq_type t_Format

val measResultSuccessHONR_r17__measResult_r17__cellResults_r17__F1 :
  measResultSuccessHONR_r17__measResult_r17__cellResults_r17__Type ->
  measQuantityResults__Type option * (measQuantityResults__Type option * unit)

val measResultSuccessHONR_r17__measResult_r17__cellResults_r17__F2 :
  seq_type -> measResultSuccessHONR_r17__measResult_r17__cellResults_r17__Type

val measResultSuccessHONR_r17__measResult_r17__cellResults_r17__Format :
  measResultSuccessHONR_r17__measResult_r17__cellResults_r17__Type t_Format

type measResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val measResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__Format_list :
  measResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__Format_Type

val measResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__list__Format :
  seq_type t_Format

val measResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__F1 :
  measResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__Type ->
  resultsPerSSB_IndexList__Type option * (resultsPerCSI_RS_IndexList__Type
  option * unit)

val measResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__F2 :
  seq_type ->
  measResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__Type

val measResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__Format :
  measResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__Type t_Format

type measResultSuccessHONR_r17__measResult_r17__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val measResultSuccessHONR_r17__measResult_r17__Format_list :
  measResultSuccessHONR_r17__measResult_r17__Format_Type

val measResultSuccessHONR_r17__measResult_r17__list__Format : seq_type t_Format

val measResultSuccessHONR_r17__measResult_r17__F1 :
  measResultSuccessHONR_r17__measResult_r17__Type ->
  measResultSuccessHONR_r17__measResult_r17__cellResults_r17__Type * (measResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__Type * unit)

val measResultSuccessHONR_r17__measResult_r17__F2 :
  seq_type -> measResultSuccessHONR_r17__measResult_r17__Type

val measResultSuccessHONR_r17__measResult_r17__Format :
  measResultSuccessHONR_r17__measResult_r17__Type t_Format

type measResultSuccessHONR_r17__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val measResultSuccessHONR_r17__Format_list :
  measResultSuccessHONR_r17__Format_Type

val measResultSuccessHONR_r17__list__Format : seq_type t_Format

val measResultSuccessHONR_r17__F1 :
  measResultSuccessHONR_r17__Type ->
  measResultSuccessHONR_r17__measResult_r17__Type * unit

val measResultSuccessHONR_r17__F2 : seq_type -> measResultSuccessHONR_r17__Type

val measResultSuccessHONR_r17__Format :
  measResultSuccessHONR_r17__Type t_Format

type sHR_Cause_r17__t304_cause_r17__Type =
| SHR_Cause_r17__t304_cause_r17__true

val sHR_Cause_r17__t304_cause_r17__nat__Format : int t_Format

val sHR_Cause_r17__t304_cause_r17__F1 :
  sHR_Cause_r17__t304_cause_r17__Type -> int

val sHR_Cause_r17__t304_cause_r17__F2 :
  int -> sHR_Cause_r17__t304_cause_r17__Type

type sHR_Cause_r17__t310_cause_r17__Type =
| SHR_Cause_r17__t310_cause_r17__true

val sHR_Cause_r17__t310_cause_r17__nat__Format : int t_Format

val sHR_Cause_r17__t310_cause_r17__F1 :
  sHR_Cause_r17__t310_cause_r17__Type -> int

val sHR_Cause_r17__t310_cause_r17__F2 :
  int -> sHR_Cause_r17__t310_cause_r17__Type

type sHR_Cause_r17__t312_cause_r17__Type =
| SHR_Cause_r17__t312_cause_r17__true

val sHR_Cause_r17__t312_cause_r17__nat__Format : int t_Format

val sHR_Cause_r17__t312_cause_r17__F1 :
  sHR_Cause_r17__t312_cause_r17__Type -> int

val sHR_Cause_r17__t312_cause_r17__F2 :
  int -> sHR_Cause_r17__t312_cause_r17__Type

type sHR_Cause_r17__sourceDAPS_Failure_r17__Type =
| SHR_Cause_r17__sourceDAPS_Failure_r17__true

val sHR_Cause_r17__sourceDAPS_Failure_r17__nat__Format : int t_Format

val sHR_Cause_r17__sourceDAPS_Failure_r17__F1 :
  sHR_Cause_r17__sourceDAPS_Failure_r17__Type -> int

val sHR_Cause_r17__sourceDAPS_Failure_r17__F2 :
  int -> sHR_Cause_r17__sourceDAPS_Failure_r17__Type

type sHR_Cause_r17__Type = { sHR_Cause_r17__t304_cause_r17 : sHR_Cause_r17__t304_cause_r17__Type
                                                             option;
                             sHR_Cause_r17__t310_cause_r17 : sHR_Cause_r17__t310_cause_r17__Type
                                                             option;
                             sHR_Cause_r17__t312_cause_r17 : sHR_Cause_r17__t312_cause_r17__Type
                                                             option;
                             sHR_Cause_r17__sourceDAPS_Failure_r17 : sHR_Cause_r17__sourceDAPS_Failure_r17__Type
                                                                     option }

val sHR_Cause_r17__root_list : seq_elem list

val sHR_Cause_r17__ext_list : typ list

val sHR_Cause_r17__t304_cause_r17__Format :
  sHR_Cause_r17__t304_cause_r17__Type t_Format

val sHR_Cause_r17__t310_cause_r17__Format :
  sHR_Cause_r17__t310_cause_r17__Type t_Format

val sHR_Cause_r17__t312_cause_r17__Format :
  sHR_Cause_r17__t312_cause_r17__Type t_Format

val sHR_Cause_r17__sourceDAPS_Failure_r17__Format :
  sHR_Cause_r17__sourceDAPS_Failure_r17__Type t_Format

type sHR_Cause_r17__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

val sHR_Cause_r17__root_Format_list : sHR_Cause_r17__root_Format_Type

type sHR_Cause_r17__ext_Format_Type = unit t_Format

val sHR_Cause_r17__ext_Format_list : sHR_Cause_r17__ext_Format_Type

type sHR_Cause_r17__list_type = seq_type * seq_ext_type

val sHR_Cause_r17__list_format : sHR_Cause_r17__list_type t_Format

val sHR_Cause_r17__F1 : sHR_Cause_r17__Type -> sHR_Cause_r17__list_type

val sHR_Cause_r17__F2 : sHR_Cause_r17__list_type -> sHR_Cause_r17__Type

val sHR_Cause_r17__Format : sHR_Cause_r17__Type t_Format

type uPInterruptionTimeAtHO_r17__Type = int

val uPInterruptionTimeAtHO_r17__Format : int t_Format

type successHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__Type =
| SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__true

val successHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__nat__Format :
  int t_Format

val successHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__F1 :
  successHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__Type -> int

val successHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__F2 :
  int -> successHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__Type

type successHO_Report_r17__sourceCellInfo_r17__Type = { successHO_Report_r17__sourceCellInfo_r17__sourcePCellId_r17 : 
                                                        cGI_Info_Logging_r16__Type;
                                                        successHO_Report_r17__sourceCellInfo_r17__sourceCellMeas_r17 : 
                                                        measResultSuccessHONR_r17__Type
                                                        option;
                                                        successHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17 : 
                                                        successHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__Type
                                                        option }

val successHO_Report_r17__sourceCellInfo_r17__list : seq_elem list

type successHO_Report_r17__targetCellInfo_r17__Type = { successHO_Report_r17__targetCellInfo_r17__targetPCellId_r17 : 
                                                        cGI_Info_Logging_r16__Type;
                                                        successHO_Report_r17__targetCellInfo_r17__targetCellMeas_r17 : 
                                                        measResultSuccessHONR_r17__Type
                                                        option }

val successHO_Report_r17__targetCellInfo_r17__list : seq_elem list

type successHO_Report_r17__measResultNeighCells_r17__Type = { successHO_Report_r17__measResultNeighCells_r17__measResultListNR_r17 : 
                                                              measResultList2NR_r16__Type
                                                              option;
                                                              successHO_Report_r17__measResultNeighCells_r17__measResultListEUTRA_r17 : 
                                                              measResultList2EUTRA_r16__Type
                                                              option }

val successHO_Report_r17__measResultNeighCells_r17__list : seq_elem list

type successHO_Report_r17__Type = { successHO_Report_r17__sourceCellInfo_r17 : 
                                    successHO_Report_r17__sourceCellInfo_r17__Type;
                                    successHO_Report_r17__targetCellInfo_r17 : 
                                    successHO_Report_r17__targetCellInfo_r17__Type;
                                    successHO_Report_r17__measResultNeighCells_r17 : 
                                    successHO_Report_r17__measResultNeighCells_r17__Type
                                    option;
                                    successHO_Report_r17__locationInfo_r17 : 
                                    locationInfo_r16__Type option;
                                    successHO_Report_r17__timeSinceCHO_Reconfig_r17 : 
                                    timeSinceCHO_Reconfig_r17__Type option;
                                    successHO_Report_r17__shr_Cause_r17 : 
                                    sHR_Cause_r17__Type option;
                                    successHO_Report_r17__ra_InformationCommon_r17 : 
                                    rA_InformationCommon_r16__Type option;
                                    successHO_Report_r17__upInterruptionTimeAtHO_r17 : 
                                    uPInterruptionTimeAtHO_r17__Type option;
                                    successHO_Report_r17__c_RNTI_r17 : 
                                    rNTI_Value__Type option }

val successHO_Report_r17__root_list : seq_elem list

val successHO_Report_r17__ext_list : typ list

val successHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__Format :
  successHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__Type t_Format

type successHO_Report_r17__sourceCellInfo_r17__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val successHO_Report_r17__sourceCellInfo_r17__Format_list :
  successHO_Report_r17__sourceCellInfo_r17__Format_Type

val successHO_Report_r17__sourceCellInfo_r17__list__Format : seq_type t_Format

val successHO_Report_r17__sourceCellInfo_r17__F1 :
  successHO_Report_r17__sourceCellInfo_r17__Type ->
  cGI_Info_Logging_r16__Type * (measResultSuccessHONR_r17__Type
  option * (successHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__Type
  option * unit))

val successHO_Report_r17__sourceCellInfo_r17__F2 :
  seq_type -> successHO_Report_r17__sourceCellInfo_r17__Type

val successHO_Report_r17__sourceCellInfo_r17__Format :
  successHO_Report_r17__sourceCellInfo_r17__Type t_Format

type successHO_Report_r17__targetCellInfo_r17__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val successHO_Report_r17__targetCellInfo_r17__Format_list :
  successHO_Report_r17__targetCellInfo_r17__Format_Type

val successHO_Report_r17__targetCellInfo_r17__list__Format : seq_type t_Format

val successHO_Report_r17__targetCellInfo_r17__F1 :
  successHO_Report_r17__targetCellInfo_r17__Type ->
  cGI_Info_Logging_r16__Type * (measResultSuccessHONR_r17__Type option * unit)

val successHO_Report_r17__targetCellInfo_r17__F2 :
  seq_type -> successHO_Report_r17__targetCellInfo_r17__Type

val successHO_Report_r17__targetCellInfo_r17__Format :
  successHO_Report_r17__targetCellInfo_r17__Type t_Format

type successHO_Report_r17__measResultNeighCells_r17__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val successHO_Report_r17__measResultNeighCells_r17__Format_list :
  successHO_Report_r17__measResultNeighCells_r17__Format_Type

val successHO_Report_r17__measResultNeighCells_r17__list__Format :
  seq_type t_Format

val successHO_Report_r17__measResultNeighCells_r17__F1 :
  successHO_Report_r17__measResultNeighCells_r17__Type ->
  measResultList2NR_r16__Type option * (measResultList2EUTRA_r16__Type
  option * unit)

val successHO_Report_r17__measResultNeighCells_r17__F2 :
  seq_type -> successHO_Report_r17__measResultNeighCells_r17__Type

val successHO_Report_r17__measResultNeighCells_r17__Format :
  successHO_Report_r17__measResultNeighCells_r17__Type t_Format

type successHO_Report_r17__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))))))))

val successHO_Report_r17__root_Format_list :
  successHO_Report_r17__root_Format_Type

type successHO_Report_r17__ext_Format_Type = unit t_Format

val successHO_Report_r17__ext_Format_list :
  successHO_Report_r17__ext_Format_Type

type successHO_Report_r17__list_type = seq_type * seq_ext_type

val successHO_Report_r17__list_format :
  successHO_Report_r17__list_type t_Format

val successHO_Report_r17__F1 :
  successHO_Report_r17__Type -> successHO_Report_r17__list_type

val successHO_Report_r17__F2 :
  successHO_Report_r17__list_type -> successHO_Report_r17__Type

val successHO_Report_r17__Format : successHO_Report_r17__Type t_Format

type connEstFailReportList_r17__Type = connEstFailReport_r16__Type list

val connEstFailReportList_r17__Format :
  connEstFailReportList_r17__Type t_Format

type uEInformationResponse_v1700_IEs__nonCriticalExtension__Type =
| Make__UEInformationResponse_v1700_IEs__nonCriticalExtension__Type

type uEInformationResponse_v1700_IEs__Type = { uEInformationResponse_v1700_IEs__successHO_Report_r17 : 
                                               successHO_Report_r17__Type
                                               option;
                                               uEInformationResponse_v1700_IEs__connEstFailReportList_r17 : 
                                               connEstFailReportList_r17__Type
                                               option;
                                               uEInformationResponse_v1700_IEs__coarseLocationInfo_r17 : 
                                               octet_string option;
                                               uEInformationResponse_v1700_IEs__nonCriticalExtension : 
                                               uEInformationResponse_v1700_IEs__nonCriticalExtension__Type
                                               option }

val uEInformationResponse_v1700_IEs__list : seq_elem list

val uEInformationResponse_v1700_IEs__nonCriticalExtension__Format :
  uEInformationResponse_v1700_IEs__nonCriticalExtension__Type t_Format

type uEInformationResponse_v1700_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

val uEInformationResponse_v1700_IEs__Format_list :
  uEInformationResponse_v1700_IEs__Format_Type

val uEInformationResponse_v1700_IEs__list__Format : seq_type t_Format

val uEInformationResponse_v1700_IEs__F1 :
  uEInformationResponse_v1700_IEs__Type -> successHO_Report_r17__Type
  option * (connEstFailReportList_r17__Type option * (octet_string
  option * (uEInformationResponse_v1700_IEs__nonCriticalExtension__Type
  option * unit)))

val uEInformationResponse_v1700_IEs__F2 :
  seq_type -> uEInformationResponse_v1700_IEs__Type

val uEInformationResponse_v1700_IEs__Format :
  uEInformationResponse_v1700_IEs__Type t_Format

type uEInformationResponse_r16_IEs__Type = { uEInformationResponse_r16_IEs__measResultIdleEUTRA_r16 : 
                                             measResultIdleEUTRA_r16__Type
                                             option;
                                             uEInformationResponse_r16_IEs__measResultIdleNR_r16 : 
                                             measResultIdleNR_r16__Type option;
                                             uEInformationResponse_r16_IEs__logMeasReport_r16 : 
                                             logMeasReport_r16__Type option;
                                             uEInformationResponse_r16_IEs__connEstFailReport_r16 : 
                                             connEstFailReport_r16__Type option;
                                             uEInformationResponse_r16_IEs__ra_ReportList_r16 : 
                                             rA_ReportList_r16__Type option;
                                             uEInformationResponse_r16_IEs__rlf_Report_r16 : 
                                             rLF_Report_r16__Type option;
                                             uEInformationResponse_r16_IEs__mobilityHistoryReport_r16 : 
                                             mobilityHistoryReport_r16__Type
                                             option;
                                             uEInformationResponse_r16_IEs__lateNonCriticalExtension : 
                                             octet_string option;
                                             uEInformationResponse_r16_IEs__nonCriticalExtension : 
                                             uEInformationResponse_v1700_IEs__Type
                                             option }

val uEInformationResponse_r16_IEs__list : seq_elem list

type uEInformationResponse_r16_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))))))))

val uEInformationResponse_r16_IEs__Format_list :
  uEInformationResponse_r16_IEs__Format_Type

val uEInformationResponse_r16_IEs__list__Format : seq_type t_Format

val uEInformationResponse_r16_IEs__F1 :
  uEInformationResponse_r16_IEs__Type -> measResultIdleEUTRA_r16__Type
  option * (measResultIdleNR_r16__Type option * (logMeasReport_r16__Type
  option * (connEstFailReport_r16__Type option * (rA_ReportList_r16__Type
  option * (rLF_Report_r16__Type option * (mobilityHistoryReport_r16__Type
  option * (octet_string option * (uEInformationResponse_v1700_IEs__Type
  option * unit))))))))

val uEInformationResponse_r16_IEs__F2 :
  seq_type -> uEInformationResponse_r16_IEs__Type

val uEInformationResponse_r16_IEs__Format :
  uEInformationResponse_r16_IEs__Type t_Format

type uEInformationResponse_r16__criticalExtensions__criticalExtensionsFuture__Type =
| Make__UEInformationResponse_r16__criticalExtensions__criticalExtensionsFuture__Type

type uEInformationResponse_r16__criticalExtensions__Type =
| UEInformationResponse_r16__criticalExtensions__ueInformationResponse_r16 of 
   uEInformationResponse_r16_IEs__Type
| UEInformationResponse_r16__criticalExtensions__criticalExtensionsFuture of 
   uEInformationResponse_r16__criticalExtensions__criticalExtensionsFuture__Type

type uEInformationResponse_r16__Type = { uEInformationResponse_r16__rrc_TransactionIdentifier : 
                                         rRC_TransactionIdentifier__Type;
                                         uEInformationResponse_r16__criticalExtensions : 
                                         uEInformationResponse_r16__criticalExtensions__Type }

val uEInformationResponse_r16__list : seq_elem list

val uEInformationResponse_r16__criticalExtensions__criticalExtensionsFuture__Format :
  uEInformationResponse_r16__criticalExtensions__criticalExtensionsFuture__Type
  t_Format

val uEInformationResponse_r16__criticalExtensions__list__Format :
  (int, __) sigT t_Format

val uEInformationResponse_r16__criticalExtensions__F1 :
  uEInformationResponse_r16__criticalExtensions__Type -> choice

val uEInformationResponse_r16__criticalExtensions__F2 :
  choice -> uEInformationResponse_r16__criticalExtensions__Type

val uEInformationResponse_r16__criticalExtensions__Format :
  uEInformationResponse_r16__criticalExtensions__Type t_Format

type uEInformationResponse_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val uEInformationResponse_r16__Format_list :
  uEInformationResponse_r16__Format_Type

val uEInformationResponse_r16__list__Format : seq_type t_Format

val uEInformationResponse_r16__F1 :
  uEInformationResponse_r16__Type ->
  rRC_TransactionIdentifier__Type * (uEInformationResponse_r16__criticalExtensions__Type * unit)

val uEInformationResponse_r16__F2 : seq_type -> uEInformationResponse_r16__Type

val uEInformationResponse_r16__Format :
  uEInformationResponse_r16__Type t_Format

type sL_InterestedFreqList_r16__Type = int list

val sL_InterestedFreqList_r16__seq_of__Format : int t_Format

val sL_InterestedFreqList_r16__Format :
  sL_InterestedFreqList_r16__Type t_Format

type sL_DestinationIdentity_r16__Type = bit_string_fixed

val sL_DestinationIdentity_r16__Format :
  sL_DestinationIdentity_r16__Type t_Format

type sL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__Type =
| SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__gbr
| SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__non_GBR
| SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__delayCriticalGBR
| SL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__spare1

val sL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__nat__Format :
  int t_Format

val sL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__F1 :
  sL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__Type -> int

val sL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__F2 :
  int -> sL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__Type

type sL_PQI_r16__sl_Non_StandardizedPQI_r16__Type = { sL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16 : 
                                                      sL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__Type
                                                      option;
                                                      sL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PriorityLevel_r16 : 
                                                      int option;
                                                      sL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketDelayBudget_r16 : 
                                                      int option;
                                                      sL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketErrorRate_r16 : 
                                                      int option;
                                                      sL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_AveragingWindow_r16 : 
                                                      int option;
                                                      sL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_MaxDataBurstVolume_r16 : 
                                                      int option }

val sL_PQI_r16__sl_Non_StandardizedPQI_r16__root_list : seq_elem list

val sL_PQI_r16__sl_Non_StandardizedPQI_r16__ext_list : typ list

type sL_PQI_r16__Type =
| SL_PQI_r16__sl_StandardizedPQI_r16 of int
| SL_PQI_r16__sl_Non_StandardizedPQI_r16 of sL_PQI_r16__sl_Non_StandardizedPQI_r16__Type

val sL_PQI_r16__sl_StandardizedPQI_r16__Format : int t_Format

val sL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__Format :
  sL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_ResourceType_r16__Type t_Format

val sL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PriorityLevel_r16__Format :
  int t_Format

val sL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketDelayBudget_r16__Format :
  int t_Format

val sL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_PacketErrorRate_r16__Format :
  int t_Format

val sL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_AveragingWindow_r16__Format :
  int t_Format

val sL_PQI_r16__sl_Non_StandardizedPQI_r16__sl_MaxDataBurstVolume_r16__Format :
  int t_Format

type sL_PQI_r16__sl_Non_StandardizedPQI_r16__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))))

val sL_PQI_r16__sl_Non_StandardizedPQI_r16__root_Format_list :
  sL_PQI_r16__sl_Non_StandardizedPQI_r16__root_Format_Type

type sL_PQI_r16__sl_Non_StandardizedPQI_r16__ext_Format_Type = unit t_Format

val sL_PQI_r16__sl_Non_StandardizedPQI_r16__ext_Format_list :
  sL_PQI_r16__sl_Non_StandardizedPQI_r16__ext_Format_Type

type sL_PQI_r16__sl_Non_StandardizedPQI_r16__list_type =
  seq_type * seq_ext_type

val sL_PQI_r16__sl_Non_StandardizedPQI_r16__list_format :
  sL_PQI_r16__sl_Non_StandardizedPQI_r16__list_type t_Format

val sL_PQI_r16__sl_Non_StandardizedPQI_r16__F1 :
  sL_PQI_r16__sl_Non_StandardizedPQI_r16__Type ->
  sL_PQI_r16__sl_Non_StandardizedPQI_r16__list_type

val sL_PQI_r16__sl_Non_StandardizedPQI_r16__F2 :
  sL_PQI_r16__sl_Non_StandardizedPQI_r16__list_type ->
  sL_PQI_r16__sl_Non_StandardizedPQI_r16__Type

val sL_PQI_r16__sl_Non_StandardizedPQI_r16__Format :
  sL_PQI_r16__sl_Non_StandardizedPQI_r16__Type t_Format

val sL_PQI_r16__list__Format : (int, __) sigT t_Format

val sL_PQI_r16__F1 : sL_PQI_r16__Type -> choice

val sL_PQI_r16__F2 : choice -> sL_PQI_r16__Type

val sL_PQI_r16__Format : sL_PQI_r16__Type t_Format

type sL_QoS_Profile_r16__Type = { sL_QoS_Profile_r16__sl_PQI_r16 : sL_PQI_r16__Type
                                                                   option;
                                  sL_QoS_Profile_r16__sl_GFBR_r16 : int option;
                                  sL_QoS_Profile_r16__sl_MFBR_r16 : int option;
                                  sL_QoS_Profile_r16__sl_Range_r16 : int option }

val sL_QoS_Profile_r16__root_list : seq_elem list

val sL_QoS_Profile_r16__ext_list : typ list

val sL_QoS_Profile_r16__sl_GFBR_r16__Format : int t_Format

val sL_QoS_Profile_r16__sl_MFBR_r16__Format : int t_Format

val sL_QoS_Profile_r16__sl_Range_r16__Format : int t_Format

type sL_QoS_Profile_r16__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

val sL_QoS_Profile_r16__root_Format_list : sL_QoS_Profile_r16__root_Format_Type

type sL_QoS_Profile_r16__ext_Format_Type = unit t_Format

val sL_QoS_Profile_r16__ext_Format_list : sL_QoS_Profile_r16__ext_Format_Type

type sL_QoS_Profile_r16__list_type = seq_type * seq_ext_type

val sL_QoS_Profile_r16__list_format : sL_QoS_Profile_r16__list_type t_Format

val sL_QoS_Profile_r16__F1 :
  sL_QoS_Profile_r16__Type -> sL_QoS_Profile_r16__list_type

val sL_QoS_Profile_r16__F2 :
  sL_QoS_Profile_r16__list_type -> sL_QoS_Profile_r16__Type

val sL_QoS_Profile_r16__Format : sL_QoS_Profile_r16__Type t_Format

type sL_QoS_Info_r16__Type = { sL_QoS_Info_r16__sl_QoS_FlowIdentity_r16 : 
                               sL_QoS_FlowIdentity_r16__Type;
                               sL_QoS_Info_r16__sl_QoS_Profile_r16 : sL_QoS_Profile_r16__Type
                                                                     option }

val sL_QoS_Info_r16__list : seq_elem list

type sL_QoS_Info_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val sL_QoS_Info_r16__Format_list : sL_QoS_Info_r16__Format_Type

val sL_QoS_Info_r16__list__Format : seq_type t_Format

val sL_QoS_Info_r16__F1 :
  sL_QoS_Info_r16__Type ->
  sL_QoS_FlowIdentity_r16__Type * (sL_QoS_Profile_r16__Type option * unit)

val sL_QoS_Info_r16__F2 : seq_type -> sL_QoS_Info_r16__Type

val sL_QoS_Info_r16__Format : sL_QoS_Info_r16__Type t_Format

type sL_RLC_ModeIndication_r16__sl_Mode_r16__Type =
| SL_RLC_ModeIndication_r16__sl_Mode_r16__sl_AM_Mode_r16 of unit
| SL_RLC_ModeIndication_r16__sl_Mode_r16__sl_UM_Mode_r16 of unit

type sL_RLC_ModeIndication_r16__sl_QoS_InfoList_r16__Type =
  sL_QoS_Info_r16__Type list

type sL_RLC_ModeIndication_r16__Type = { sL_RLC_ModeIndication_r16__sl_Mode_r16 : 
                                         sL_RLC_ModeIndication_r16__sl_Mode_r16__Type;
                                         sL_RLC_ModeIndication_r16__sl_QoS_InfoList_r16 : 
                                         sL_RLC_ModeIndication_r16__sl_QoS_InfoList_r16__Type }

val sL_RLC_ModeIndication_r16__list : seq_elem list

val sL_RLC_ModeIndication_r16__sl_Mode_r16__list__Format :
  (int, __) sigT t_Format

val sL_RLC_ModeIndication_r16__sl_Mode_r16__F1 :
  sL_RLC_ModeIndication_r16__sl_Mode_r16__Type -> choice

val sL_RLC_ModeIndication_r16__sl_Mode_r16__F2 :
  choice -> sL_RLC_ModeIndication_r16__sl_Mode_r16__Type

val sL_RLC_ModeIndication_r16__sl_Mode_r16__Format :
  sL_RLC_ModeIndication_r16__sl_Mode_r16__Type t_Format

val sL_RLC_ModeIndication_r16__sl_QoS_InfoList_r16__Format :
  sL_RLC_ModeIndication_r16__sl_QoS_InfoList_r16__Type t_Format

type sL_RLC_ModeIndication_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val sL_RLC_ModeIndication_r16__Format_list :
  sL_RLC_ModeIndication_r16__Format_Type

val sL_RLC_ModeIndication_r16__list__Format : seq_type t_Format

val sL_RLC_ModeIndication_r16__F1 :
  sL_RLC_ModeIndication_r16__Type ->
  sL_RLC_ModeIndication_r16__sl_Mode_r16__Type * (sL_RLC_ModeIndication_r16__sl_QoS_InfoList_r16__Type * unit)

val sL_RLC_ModeIndication_r16__F2 : seq_type -> sL_RLC_ModeIndication_r16__Type

val sL_RLC_ModeIndication_r16__Format :
  sL_RLC_ModeIndication_r16__Type t_Format

type sL_TypeTxSync_r16__Type =
| SL_TypeTxSync_r16__gnss
| SL_TypeTxSync_r16__gnbEnb
| SL_TypeTxSync_r16__ue

val sL_TypeTxSync_r16__nat__Format : int t_Format

val sL_TypeTxSync_r16__F1 : sL_TypeTxSync_r16__Type -> int

val sL_TypeTxSync_r16__F2 : int -> sL_TypeTxSync_r16__Type

val sL_TypeTxSync_r16__Format : sL_TypeTxSync_r16__Type t_Format

type sL_TxInterestedFreqList_r16__Type = int list

val sL_TxInterestedFreqList_r16__seq_of__Format : int t_Format

val sL_TxInterestedFreqList_r16__Format :
  sL_TxInterestedFreqList_r16__Type t_Format

type sL_TxResourceReq_r16__sl_CastType_r16__Type =
| SL_TxResourceReq_r16__sl_CastType_r16__broadcast
| SL_TxResourceReq_r16__sl_CastType_r16__groupcast
| SL_TxResourceReq_r16__sl_CastType_r16__unicast
| SL_TxResourceReq_r16__sl_CastType_r16__spare1

val sL_TxResourceReq_r16__sl_CastType_r16__nat__Format : int t_Format

val sL_TxResourceReq_r16__sl_CastType_r16__F1 :
  sL_TxResourceReq_r16__sl_CastType_r16__Type -> int

val sL_TxResourceReq_r16__sl_CastType_r16__F2 :
  int -> sL_TxResourceReq_r16__sl_CastType_r16__Type

type sL_TxResourceReq_r16__sl_RLC_ModeIndicationList_r16__Type =
  sL_RLC_ModeIndication_r16__Type list

type sL_TxResourceReq_r16__sl_QoS_InfoList_r16__Type =
  sL_QoS_Info_r16__Type list

type sL_TxResourceReq_r16__sl_TypeTxSyncList_r16__Type =
  sL_TypeTxSync_r16__Type list

type sL_TxResourceReq_r16__Type = { sL_TxResourceReq_r16__sl_DestinationIdentity_r16 : 
                                    sL_DestinationIdentity_r16__Type;
                                    sL_TxResourceReq_r16__sl_CastType_r16 : 
                                    sL_TxResourceReq_r16__sl_CastType_r16__Type;
                                    sL_TxResourceReq_r16__sl_RLC_ModeIndicationList_r16 : 
                                    sL_TxResourceReq_r16__sl_RLC_ModeIndicationList_r16__Type
                                    option;
                                    sL_TxResourceReq_r16__sl_QoS_InfoList_r16 : 
                                    sL_TxResourceReq_r16__sl_QoS_InfoList_r16__Type
                                    option;
                                    sL_TxResourceReq_r16__sl_TypeTxSyncList_r16 : 
                                    sL_TxResourceReq_r16__sl_TypeTxSyncList_r16__Type
                                    option;
                                    sL_TxResourceReq_r16__sl_TxInterestedFreqList_r16 : 
                                    sL_TxInterestedFreqList_r16__Type option;
                                    sL_TxResourceReq_r16__sl_CapabilityInformationSidelink_r16 : 
                                    octet_string option }

val sL_TxResourceReq_r16__list : seq_elem list

val sL_TxResourceReq_r16__sl_CastType_r16__Format :
  sL_TxResourceReq_r16__sl_CastType_r16__Type t_Format

val sL_TxResourceReq_r16__sl_RLC_ModeIndicationList_r16__Format :
  sL_TxResourceReq_r16__sl_RLC_ModeIndicationList_r16__Type t_Format

val sL_TxResourceReq_r16__sl_QoS_InfoList_r16__Format :
  sL_TxResourceReq_r16__sl_QoS_InfoList_r16__Type t_Format

val sL_TxResourceReq_r16__sl_TypeTxSyncList_r16__Format :
  sL_TxResourceReq_r16__sl_TypeTxSyncList_r16__Type t_Format

type sL_TxResourceReq_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))))))

val sL_TxResourceReq_r16__Format_list : sL_TxResourceReq_r16__Format_Type

val sL_TxResourceReq_r16__list__Format : seq_type t_Format

val sL_TxResourceReq_r16__F1 :
  sL_TxResourceReq_r16__Type ->
  sL_DestinationIdentity_r16__Type * (sL_TxResourceReq_r16__sl_CastType_r16__Type * (sL_TxResourceReq_r16__sl_RLC_ModeIndicationList_r16__Type
  option * (sL_TxResourceReq_r16__sl_QoS_InfoList_r16__Type
  option * (sL_TxResourceReq_r16__sl_TypeTxSyncList_r16__Type
  option * (sL_TxInterestedFreqList_r16__Type option * (octet_string
  option * unit))))))

val sL_TxResourceReq_r16__F2 : seq_type -> sL_TxResourceReq_r16__Type

val sL_TxResourceReq_r16__Format : sL_TxResourceReq_r16__Type t_Format

type sL_TxResourceReqList_r16__Type = sL_TxResourceReq_r16__Type list

val sL_TxResourceReqList_r16__Format : sL_TxResourceReqList_r16__Type t_Format

type sL_Failure_r16__sl_Failure_r16__Type =
| SL_Failure_r16__sl_Failure_r16__rlf
| SL_Failure_r16__sl_Failure_r16__configFailure
| SL_Failure_r16__sl_Failure_r16__drxReject_v1710
| SL_Failure_r16__sl_Failure_r16__spare5
| SL_Failure_r16__sl_Failure_r16__spare4
| SL_Failure_r16__sl_Failure_r16__spare3
| SL_Failure_r16__sl_Failure_r16__spare2
| SL_Failure_r16__sl_Failure_r16__spare1

val sL_Failure_r16__sl_Failure_r16__nat__Format : int t_Format

val sL_Failure_r16__sl_Failure_r16__F1 :
  sL_Failure_r16__sl_Failure_r16__Type -> int

val sL_Failure_r16__sl_Failure_r16__F2 :
  int -> sL_Failure_r16__sl_Failure_r16__Type

type sL_Failure_r16__Type = { sL_Failure_r16__sl_DestinationIdentity_r16 : 
                              sL_DestinationIdentity_r16__Type;
                              sL_Failure_r16__sl_Failure_r16 : sL_Failure_r16__sl_Failure_r16__Type }

val sL_Failure_r16__list : seq_elem list

val sL_Failure_r16__sl_Failure_r16__Format :
  sL_Failure_r16__sl_Failure_r16__Type t_Format

type sL_Failure_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val sL_Failure_r16__Format_list : sL_Failure_r16__Format_Type

val sL_Failure_r16__list__Format : seq_type t_Format

val sL_Failure_r16__F1 :
  sL_Failure_r16__Type ->
  sL_DestinationIdentity_r16__Type * (sL_Failure_r16__sl_Failure_r16__Type * unit)

val sL_Failure_r16__F2 : seq_type -> sL_Failure_r16__Type

val sL_Failure_r16__Format : sL_Failure_r16__Type t_Format

type sL_FailureList_r16__Type = sL_Failure_r16__Type list

val sL_FailureList_r16__Format : sL_FailureList_r16__Type t_Format

type sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__Type =
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms1
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms2
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms3
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms4
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms5
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms6
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms8
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms10
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms20
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms30
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms40
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms50
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms60
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms80
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms100
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms200
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms300
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms400
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms500
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms600
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms800
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms1000
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms1200
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms1600
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__spare8
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__spare7
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__spare6
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__spare5
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__spare4
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__spare3
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__spare2
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__spare1

val sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__nat__Format :
  int t_Format

val sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__F1 :
  sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__Type
  -> int

val sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__F2 :
  int ->
  sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__Type

type sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__Type =
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__subMilliSeconds of 
   int
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds of 
   sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__Type

type sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__Type =
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms10 of int
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms20 of int
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms32 of int
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms40 of int
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms60 of int
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms64 of int
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms70 of int
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms80 of int
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms128 of int
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms160 of int
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms256 of int
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms320 of int
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms512 of int
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms640 of int
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms1024 of int
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms1280 of int
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms2048 of int
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms2560 of int
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms5120 of int
| SL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms10240 of int

type sL_DRX_ConfigUC_SemiStatic_r17__Type = { sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17 : 
                                              sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__Type;
                                              sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17 : 
                                              sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__Type;
                                              sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_SlotOffset_r17 : 
                                              int }

val sL_DRX_ConfigUC_SemiStatic_r17__list : seq_elem list

val sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__subMilliSeconds__Format :
  int t_Format

val sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__Format :
  sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__milliSeconds__Type
  t_Format

val sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__list__Format :
  (int, __) sigT t_Format

val sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__F1 :
  sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__Type -> choice

val sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__F2 :
  choice -> sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__Type

val sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__Format :
  sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__Type t_Format

val sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms10__Format :
  int t_Format

val sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms20__Format :
  int t_Format

val sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms32__Format :
  int t_Format

val sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms40__Format :
  int t_Format

val sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms60__Format :
  int t_Format

val sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms64__Format :
  int t_Format

val sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms70__Format :
  int t_Format

val sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms80__Format :
  int t_Format

val sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms128__Format :
  int t_Format

val sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms160__Format :
  int t_Format

val sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms256__Format :
  int t_Format

val sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms320__Format :
  int t_Format

val sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms512__Format :
  int t_Format

val sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms640__Format :
  int t_Format

val sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms1024__Format :
  int t_Format

val sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms1280__Format :
  int t_Format

val sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms2048__Format :
  int t_Format

val sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms2560__Format :
  int t_Format

val sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms5120__Format :
  int t_Format

val sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__ms10240__Format :
  int t_Format

val sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__list__Format :
  (int, __) sigT t_Format

val sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__F1 :
  sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__Type -> choice

val sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__F2 :
  choice -> sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__Type

val sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__Format :
  sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__Type t_Format

val sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_SlotOffset_r17__Format :
  int t_Format

type sL_DRX_ConfigUC_SemiStatic_r17__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val sL_DRX_ConfigUC_SemiStatic_r17__Format_list :
  sL_DRX_ConfigUC_SemiStatic_r17__Format_Type

val sL_DRX_ConfigUC_SemiStatic_r17__list__Format : seq_type t_Format

val sL_DRX_ConfigUC_SemiStatic_r17__F1 :
  sL_DRX_ConfigUC_SemiStatic_r17__Type ->
  sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_onDurationTimer_r17__Type * (sL_DRX_ConfigUC_SemiStatic_r17__sl_drx_CycleStartOffset_r17__Type * (int * unit))

val sL_DRX_ConfigUC_SemiStatic_r17__F2 :
  seq_type -> sL_DRX_ConfigUC_SemiStatic_r17__Type

val sL_DRX_ConfigUC_SemiStatic_r17__Format :
  sL_DRX_ConfigUC_SemiStatic_r17__Type t_Format

type sL_TxResourceReq_v1700__sl_DRX_InfoFromRxList_r17__Type =
  sL_DRX_ConfigUC_SemiStatic_r17__Type list

type sL_TxResourceReq_v1700__sl_DRX_Indication_r17__Type =
| SL_TxResourceReq_v1700__sl_DRX_Indication_r17__on
| SL_TxResourceReq_v1700__sl_DRX_Indication_r17__off

val sL_TxResourceReq_v1700__sl_DRX_Indication_r17__nat__Format : int t_Format

val sL_TxResourceReq_v1700__sl_DRX_Indication_r17__F1 :
  sL_TxResourceReq_v1700__sl_DRX_Indication_r17__Type -> int

val sL_TxResourceReq_v1700__sl_DRX_Indication_r17__F2 :
  int -> sL_TxResourceReq_v1700__sl_DRX_Indication_r17__Type

type sL_TxResourceReq_v1700__Type = { sL_TxResourceReq_v1700__sl_DRX_InfoFromRxList_r17 : 
                                      sL_TxResourceReq_v1700__sl_DRX_InfoFromRxList_r17__Type
                                      option;
                                      sL_TxResourceReq_v1700__sl_DRX_Indication_r17 : 
                                      sL_TxResourceReq_v1700__sl_DRX_Indication_r17__Type
                                      option }

val sL_TxResourceReq_v1700__root_list : seq_elem list

val sL_TxResourceReq_v1700__ext_list : typ list

val sL_TxResourceReq_v1700__sl_DRX_InfoFromRxList_r17__Format :
  sL_TxResourceReq_v1700__sl_DRX_InfoFromRxList_r17__Type t_Format

val sL_TxResourceReq_v1700__sl_DRX_Indication_r17__Format :
  sL_TxResourceReq_v1700__sl_DRX_Indication_r17__Type t_Format

type sL_TxResourceReq_v1700__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val sL_TxResourceReq_v1700__root_Format_list :
  sL_TxResourceReq_v1700__root_Format_Type

type sL_TxResourceReq_v1700__ext_Format_Type = unit t_Format

val sL_TxResourceReq_v1700__ext_Format_list :
  sL_TxResourceReq_v1700__ext_Format_Type

type sL_TxResourceReq_v1700__list_type = seq_type * seq_ext_type

val sL_TxResourceReq_v1700__list_format :
  sL_TxResourceReq_v1700__list_type t_Format

val sL_TxResourceReq_v1700__F1 :
  sL_TxResourceReq_v1700__Type -> sL_TxResourceReq_v1700__list_type

val sL_TxResourceReq_v1700__F2 :
  sL_TxResourceReq_v1700__list_type -> sL_TxResourceReq_v1700__Type

val sL_TxResourceReq_v1700__Format : sL_TxResourceReq_v1700__Type t_Format

type sL_TxResourceReqList_v1700__Type = sL_TxResourceReq_v1700__Type list

val sL_TxResourceReqList_v1700__Format :
  sL_TxResourceReqList_v1700__Type t_Format

type sL_RxDRX_Report_v1700__Type = { sL_RxDRX_Report_v1700__sl_DRX_ConfigFromTx_r17 : 
                                     sL_DRX_ConfigUC_SemiStatic_r17__Type }

val sL_RxDRX_Report_v1700__root_list : seq_elem list

val sL_RxDRX_Report_v1700__ext_list : typ list

type sL_RxDRX_Report_v1700__root_Format_Type =
  seq_elem_to_format * seq_elem_to_format

val sL_RxDRX_Report_v1700__root_Format_list :
  sL_RxDRX_Report_v1700__root_Format_Type

type sL_RxDRX_Report_v1700__ext_Format_Type = unit t_Format

val sL_RxDRX_Report_v1700__ext_Format_list :
  sL_RxDRX_Report_v1700__ext_Format_Type

type sL_RxDRX_Report_v1700__list_type = seq_type * seq_ext_type

val sL_RxDRX_Report_v1700__list_format :
  sL_RxDRX_Report_v1700__list_type t_Format

val sL_RxDRX_Report_v1700__F1 :
  sL_RxDRX_Report_v1700__Type -> sL_RxDRX_Report_v1700__list_type

val sL_RxDRX_Report_v1700__F2 :
  sL_RxDRX_Report_v1700__list_type -> sL_RxDRX_Report_v1700__Type

val sL_RxDRX_Report_v1700__Format : sL_RxDRX_Report_v1700__Type t_Format

type sL_RxDRX_ReportList_v1700__Type = sL_RxDRX_Report_v1700__Type list

val sL_RxDRX_ReportList_v1700__Format :
  sL_RxDRX_ReportList_v1700__Type t_Format

type sL_RxInterestedGC_BC_Dest_r17__sl_RxInterestedQoS_InfoList_r17__Type =
  sL_QoS_Info_r16__Type list

type sL_RxInterestedGC_BC_Dest_r17__Type = { sL_RxInterestedGC_BC_Dest_r17__sl_RxInterestedQoS_InfoList_r17 : 
                                             sL_RxInterestedGC_BC_Dest_r17__sl_RxInterestedQoS_InfoList_r17__Type;
                                             sL_RxInterestedGC_BC_Dest_r17__sl_DestinationIdentity_r16 : 
                                             sL_DestinationIdentity_r16__Type }

val sL_RxInterestedGC_BC_Dest_r17__list : seq_elem list

val sL_RxInterestedGC_BC_Dest_r17__sl_RxInterestedQoS_InfoList_r17__Format :
  sL_RxInterestedGC_BC_Dest_r17__sl_RxInterestedQoS_InfoList_r17__Type t_Format

type sL_RxInterestedGC_BC_Dest_r17__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val sL_RxInterestedGC_BC_Dest_r17__Format_list :
  sL_RxInterestedGC_BC_Dest_r17__Format_Type

val sL_RxInterestedGC_BC_Dest_r17__list__Format : seq_type t_Format

val sL_RxInterestedGC_BC_Dest_r17__F1 :
  sL_RxInterestedGC_BC_Dest_r17__Type ->
  sL_RxInterestedGC_BC_Dest_r17__sl_RxInterestedQoS_InfoList_r17__Type * (sL_DestinationIdentity_r16__Type * unit)

val sL_RxInterestedGC_BC_Dest_r17__F2 :
  seq_type -> sL_RxInterestedGC_BC_Dest_r17__Type

val sL_RxInterestedGC_BC_Dest_r17__Format :
  sL_RxInterestedGC_BC_Dest_r17__Type t_Format

type sL_RxInterestedGC_BC_DestList_r17__Type =
  sL_RxInterestedGC_BC_Dest_r17__Type list

val sL_RxInterestedGC_BC_DestList_r17__Format :
  sL_RxInterestedGC_BC_DestList_r17__Type t_Format

type sL_SourceIdentity_r17__Type = bit_string_fixed

val sL_SourceIdentity_r17__Format : sL_SourceIdentity_r17__Type t_Format

type sL_TxResourceReqDisc_r17__sl_CastTypeDisc_r17__Type =
| SL_TxResourceReqDisc_r17__sl_CastTypeDisc_r17__broadcast
| SL_TxResourceReqDisc_r17__sl_CastTypeDisc_r17__groupcast
| SL_TxResourceReqDisc_r17__sl_CastTypeDisc_r17__unicast
| SL_TxResourceReqDisc_r17__sl_CastTypeDisc_r17__spare1

val sL_TxResourceReqDisc_r17__sl_CastTypeDisc_r17__nat__Format : int t_Format

val sL_TxResourceReqDisc_r17__sl_CastTypeDisc_r17__F1 :
  sL_TxResourceReqDisc_r17__sl_CastTypeDisc_r17__Type -> int

val sL_TxResourceReqDisc_r17__sl_CastTypeDisc_r17__F2 :
  int -> sL_TxResourceReqDisc_r17__sl_CastTypeDisc_r17__Type

type sL_TxResourceReqDisc_r17__sl_TypeTxSyncListDisc_r17__Type =
  sL_TypeTxSync_r16__Type list

type sL_TxResourceReqDisc_r17__sl_DiscoveryType_r17__Type =
| SL_TxResourceReqDisc_r17__sl_DiscoveryType_r17__relay
| SL_TxResourceReqDisc_r17__sl_DiscoveryType_r17__non_Relay

val sL_TxResourceReqDisc_r17__sl_DiscoveryType_r17__nat__Format : int t_Format

val sL_TxResourceReqDisc_r17__sl_DiscoveryType_r17__F1 :
  sL_TxResourceReqDisc_r17__sl_DiscoveryType_r17__Type -> int

val sL_TxResourceReqDisc_r17__sl_DiscoveryType_r17__F2 :
  int -> sL_TxResourceReqDisc_r17__sl_DiscoveryType_r17__Type

type sL_TxResourceReqDisc_r17__Type = { sL_TxResourceReqDisc_r17__sl_DestinationIdentityDisc_r17 : 
                                        sL_DestinationIdentity_r16__Type;
                                        sL_TxResourceReqDisc_r17__sl_SourceIdentityRelayUE_r17 : 
                                        sL_SourceIdentity_r17__Type option;
                                        sL_TxResourceReqDisc_r17__sl_CastTypeDisc_r17 : 
                                        sL_TxResourceReqDisc_r17__sl_CastTypeDisc_r17__Type;
                                        sL_TxResourceReqDisc_r17__sl_TxInterestedFreqListDisc_r17 : 
                                        sL_TxInterestedFreqList_r16__Type;
                                        sL_TxResourceReqDisc_r17__sl_TypeTxSyncListDisc_r17 : 
                                        sL_TxResourceReqDisc_r17__sl_TypeTxSyncListDisc_r17__Type;
                                        sL_TxResourceReqDisc_r17__sl_DiscoveryType_r17 : 
                                        sL_TxResourceReqDisc_r17__sl_DiscoveryType_r17__Type }

val sL_TxResourceReqDisc_r17__root_list : seq_elem list

val sL_TxResourceReqDisc_r17__ext_list : typ list

val sL_TxResourceReqDisc_r17__sl_CastTypeDisc_r17__Format :
  sL_TxResourceReqDisc_r17__sl_CastTypeDisc_r17__Type t_Format

val sL_TxResourceReqDisc_r17__sl_TypeTxSyncListDisc_r17__Format :
  sL_TxResourceReqDisc_r17__sl_TypeTxSyncListDisc_r17__Type t_Format

val sL_TxResourceReqDisc_r17__sl_DiscoveryType_r17__Format :
  sL_TxResourceReqDisc_r17__sl_DiscoveryType_r17__Type t_Format

type sL_TxResourceReqDisc_r17__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))))

val sL_TxResourceReqDisc_r17__root_Format_list :
  sL_TxResourceReqDisc_r17__root_Format_Type

type sL_TxResourceReqDisc_r17__ext_Format_Type = unit t_Format

val sL_TxResourceReqDisc_r17__ext_Format_list :
  sL_TxResourceReqDisc_r17__ext_Format_Type

type sL_TxResourceReqDisc_r17__list_type = seq_type * seq_ext_type

val sL_TxResourceReqDisc_r17__list_format :
  sL_TxResourceReqDisc_r17__list_type t_Format

val sL_TxResourceReqDisc_r17__F1 :
  sL_TxResourceReqDisc_r17__Type -> sL_TxResourceReqDisc_r17__list_type

val sL_TxResourceReqDisc_r17__F2 :
  sL_TxResourceReqDisc_r17__list_type -> sL_TxResourceReqDisc_r17__Type

val sL_TxResourceReqDisc_r17__Format : sL_TxResourceReqDisc_r17__Type t_Format

type sL_TxResourceReqListDisc_r17__Type = sL_TxResourceReqDisc_r17__Type list

val sL_TxResourceReqListDisc_r17__Format :
  sL_TxResourceReqListDisc_r17__Type t_Format

type i_RNTI_Value__Type = bit_string_fixed

val i_RNTI_Value__Format : i_RNTI_Value__Type t_Format

type sL_PagingIdentityRemoteUE_r17__Type = { sL_PagingIdentityRemoteUE_r17__ng_5G_S_TMSI_r17 : 
                                             nG_5G_S_TMSI__Type;
                                             sL_PagingIdentityRemoteUE_r17__fullI_RNTI_r17 : 
                                             i_RNTI_Value__Type option }

val sL_PagingIdentityRemoteUE_r17__list : seq_elem list

type sL_PagingIdentityRemoteUE_r17__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val sL_PagingIdentityRemoteUE_r17__Format_list :
  sL_PagingIdentityRemoteUE_r17__Format_Type

val sL_PagingIdentityRemoteUE_r17__list__Format : seq_type t_Format

val sL_PagingIdentityRemoteUE_r17__F1 :
  sL_PagingIdentityRemoteUE_r17__Type ->
  nG_5G_S_TMSI__Type * (i_RNTI_Value__Type option * unit)

val sL_PagingIdentityRemoteUE_r17__F2 :
  seq_type -> sL_PagingIdentityRemoteUE_r17__Type

val sL_PagingIdentityRemoteUE_r17__Format :
  sL_PagingIdentityRemoteUE_r17__Type t_Format

type sL_TxResourceReqL2U2N_Relay_r17__sl_TypeTxSyncListL2U2N_r17__Type =
  sL_TypeTxSync_r16__Type list

type sL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__Type =
| SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__true

val sL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__nat__Format :
  int t_Format

val sL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__F1 :
  sL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__Type -> int

val sL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__F2 :
  int -> sL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__Type

type sL_TxResourceReqL2U2N_Relay_r17__Type = { sL_TxResourceReqL2U2N_Relay_r17__sl_DestinationIdentityL2U2N_r17 : 
                                               sL_DestinationIdentity_r16__Type
                                               option;
                                               sL_TxResourceReqL2U2N_Relay_r17__sl_TxInterestedFreqListL2U2N_r17 : 
                                               sL_TxInterestedFreqList_r16__Type;
                                               sL_TxResourceReqL2U2N_Relay_r17__sl_TypeTxSyncListL2U2N_r17 : 
                                               sL_TxResourceReqL2U2N_Relay_r17__sl_TypeTxSyncListL2U2N_r17__Type;
                                               sL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17 : 
                                               sL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__Type
                                               option;
                                               sL_TxResourceReqL2U2N_Relay_r17__sl_PagingIdentityRemoteUE_r17 : 
                                               sL_PagingIdentityRemoteUE_r17__Type
                                               option;
                                               sL_TxResourceReqL2U2N_Relay_r17__sl_CapabilityInformationSidelink_r17 : 
                                               octet_string option }

val sL_TxResourceReqL2U2N_Relay_r17__root_list : seq_elem list

val sL_TxResourceReqL2U2N_Relay_r17__ext_list : typ list

val sL_TxResourceReqL2U2N_Relay_r17__sl_TypeTxSyncListL2U2N_r17__Format :
  sL_TxResourceReqL2U2N_Relay_r17__sl_TypeTxSyncListL2U2N_r17__Type t_Format

val sL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__Format :
  sL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__Type t_Format

type sL_TxResourceReqL2U2N_Relay_r17__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))))

val sL_TxResourceReqL2U2N_Relay_r17__root_Format_list :
  sL_TxResourceReqL2U2N_Relay_r17__root_Format_Type

type sL_TxResourceReqL2U2N_Relay_r17__ext_Format_Type = unit t_Format

val sL_TxResourceReqL2U2N_Relay_r17__ext_Format_list :
  sL_TxResourceReqL2U2N_Relay_r17__ext_Format_Type

type sL_TxResourceReqL2U2N_Relay_r17__list_type = seq_type * seq_ext_type

val sL_TxResourceReqL2U2N_Relay_r17__list_format :
  sL_TxResourceReqL2U2N_Relay_r17__list_type t_Format

val sL_TxResourceReqL2U2N_Relay_r17__F1 :
  sL_TxResourceReqL2U2N_Relay_r17__Type ->
  sL_TxResourceReqL2U2N_Relay_r17__list_type

val sL_TxResourceReqL2U2N_Relay_r17__F2 :
  sL_TxResourceReqL2U2N_Relay_r17__list_type ->
  sL_TxResourceReqL2U2N_Relay_r17__Type

val sL_TxResourceReqL2U2N_Relay_r17__Format :
  sL_TxResourceReqL2U2N_Relay_r17__Type t_Format

type sL_TxResourceReqCommRelay_r17__Type =
| SL_TxResourceReqCommRelay_r17__sl_TxResourceReqL2U2N_Relay_r17 of sL_TxResourceReqL2U2N_Relay_r17__Type
| SL_TxResourceReqCommRelay_r17__sl_TxResourceReqL3U2N_Relay_r17 of sL_TxResourceReq_r16__Type

val sL_TxResourceReqCommRelay_r17__list__Format : (int, __) sigT t_Format

val sL_TxResourceReqCommRelay_r17__F1 :
  sL_TxResourceReqCommRelay_r17__Type -> choice

val sL_TxResourceReqCommRelay_r17__F2 :
  choice -> sL_TxResourceReqCommRelay_r17__Type

val sL_TxResourceReqCommRelay_r17__Format :
  sL_TxResourceReqCommRelay_r17__Type t_Format

type sL_TxResourceReqCommRelayInfo_r17__Type = { sL_TxResourceReqCommRelayInfo_r17__sl_RelayDRXConfig_r17 : 
                                                 sL_TxResourceReq_v1700__Type
                                                 option;
                                                 sL_TxResourceReqCommRelayInfo_r17__sl_TxResourceReqCommRelay_r17 : 
                                                 sL_TxResourceReqCommRelay_r17__Type }

val sL_TxResourceReqCommRelayInfo_r17__list : seq_elem list

type sL_TxResourceReqCommRelayInfo_r17__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val sL_TxResourceReqCommRelayInfo_r17__Format_list :
  sL_TxResourceReqCommRelayInfo_r17__Format_Type

val sL_TxResourceReqCommRelayInfo_r17__list__Format : seq_type t_Format

val sL_TxResourceReqCommRelayInfo_r17__F1 :
  sL_TxResourceReqCommRelayInfo_r17__Type -> sL_TxResourceReq_v1700__Type
  option * (sL_TxResourceReqCommRelay_r17__Type * unit)

val sL_TxResourceReqCommRelayInfo_r17__F2 :
  seq_type -> sL_TxResourceReqCommRelayInfo_r17__Type

val sL_TxResourceReqCommRelayInfo_r17__Format :
  sL_TxResourceReqCommRelayInfo_r17__Type t_Format

type sL_TxResourceReqListCommRelay_r17__Type =
  sL_TxResourceReqCommRelayInfo_r17__Type list

val sL_TxResourceReqListCommRelay_r17__Format :
  sL_TxResourceReqListCommRelay_r17__Type t_Format

type sidelinkUEInformationNR_v1700_IEs__ue_Type_r17__Type =
| SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__relayUE
| SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__remoteUE

val sidelinkUEInformationNR_v1700_IEs__ue_Type_r17__nat__Format : int t_Format

val sidelinkUEInformationNR_v1700_IEs__ue_Type_r17__F1 :
  sidelinkUEInformationNR_v1700_IEs__ue_Type_r17__Type -> int

val sidelinkUEInformationNR_v1700_IEs__ue_Type_r17__F2 :
  int -> sidelinkUEInformationNR_v1700_IEs__ue_Type_r17__Type

type sidelinkUEInformationNR_v1700_IEs__nonCriticalExtension__Type =
| Make__SidelinkUEInformationNR_v1700_IEs__nonCriticalExtension__Type

type sidelinkUEInformationNR_v1700_IEs__Type = { sidelinkUEInformationNR_v1700_IEs__sl_TxResourceReqList_v1700 : 
                                                 sL_TxResourceReqList_v1700__Type
                                                 option;
                                                 sidelinkUEInformationNR_v1700_IEs__sl_RxDRX_ReportList_v1700 : 
                                                 sL_RxDRX_ReportList_v1700__Type
                                                 option;
                                                 sidelinkUEInformationNR_v1700_IEs__sl_RxInterestedGC_BC_DestList_r17 : 
                                                 sL_RxInterestedGC_BC_DestList_r17__Type
                                                 option;
                                                 sidelinkUEInformationNR_v1700_IEs__sl_RxInterestedFreqListDisc_r17 : 
                                                 sL_InterestedFreqList_r16__Type
                                                 option;
                                                 sidelinkUEInformationNR_v1700_IEs__sl_TxResourceReqListDisc_r17 : 
                                                 sL_TxResourceReqListDisc_r17__Type
                                                 option;
                                                 sidelinkUEInformationNR_v1700_IEs__sl_TxResourceReqListCommRelay_r17 : 
                                                 sL_TxResourceReqListCommRelay_r17__Type
                                                 option;
                                                 sidelinkUEInformationNR_v1700_IEs__ue_Type_r17 : 
                                                 sidelinkUEInformationNR_v1700_IEs__ue_Type_r17__Type
                                                 option;
                                                 sidelinkUEInformationNR_v1700_IEs__sl_SourceIdentityRemoteUE_r17 : 
                                                 sL_SourceIdentity_r17__Type
                                                 option;
                                                 sidelinkUEInformationNR_v1700_IEs__nonCriticalExtension : 
                                                 sidelinkUEInformationNR_v1700_IEs__nonCriticalExtension__Type
                                                 option }

val sidelinkUEInformationNR_v1700_IEs__list : seq_elem list

val sidelinkUEInformationNR_v1700_IEs__ue_Type_r17__Format :
  sidelinkUEInformationNR_v1700_IEs__ue_Type_r17__Type t_Format

val sidelinkUEInformationNR_v1700_IEs__nonCriticalExtension__Format :
  sidelinkUEInformationNR_v1700_IEs__nonCriticalExtension__Type t_Format

type sidelinkUEInformationNR_v1700_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))))))))

val sidelinkUEInformationNR_v1700_IEs__Format_list :
  sidelinkUEInformationNR_v1700_IEs__Format_Type

val sidelinkUEInformationNR_v1700_IEs__list__Format : seq_type t_Format

val sidelinkUEInformationNR_v1700_IEs__F1 :
  sidelinkUEInformationNR_v1700_IEs__Type -> sL_TxResourceReqList_v1700__Type
  option * (sL_RxDRX_ReportList_v1700__Type
  option * (sL_RxInterestedGC_BC_DestList_r17__Type
  option * (sL_InterestedFreqList_r16__Type
  option * (sL_TxResourceReqListDisc_r17__Type
  option * (sL_TxResourceReqListCommRelay_r17__Type
  option * (sidelinkUEInformationNR_v1700_IEs__ue_Type_r17__Type
  option * (sL_SourceIdentity_r17__Type
  option * (sidelinkUEInformationNR_v1700_IEs__nonCriticalExtension__Type
  option * unit))))))))

val sidelinkUEInformationNR_v1700_IEs__F2 :
  seq_type -> sidelinkUEInformationNR_v1700_IEs__Type

val sidelinkUEInformationNR_v1700_IEs__Format :
  sidelinkUEInformationNR_v1700_IEs__Type t_Format

type sidelinkUEInformationNR_r16_IEs__Type = { sidelinkUEInformationNR_r16_IEs__sl_RxInterestedFreqList_r16 : 
                                               sL_InterestedFreqList_r16__Type
                                               option;
                                               sidelinkUEInformationNR_r16_IEs__sl_TxResourceReqList_r16 : 
                                               sL_TxResourceReqList_r16__Type
                                               option;
                                               sidelinkUEInformationNR_r16_IEs__sl_FailureList_r16 : 
                                               sL_FailureList_r16__Type option;
                                               sidelinkUEInformationNR_r16_IEs__lateNonCriticalExtension : 
                                               octet_string option;
                                               sidelinkUEInformationNR_r16_IEs__nonCriticalExtension : 
                                               sidelinkUEInformationNR_v1700_IEs__Type
                                               option }

val sidelinkUEInformationNR_r16_IEs__list : seq_elem list

type sidelinkUEInformationNR_r16_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))))

val sidelinkUEInformationNR_r16_IEs__Format_list :
  sidelinkUEInformationNR_r16_IEs__Format_Type

val sidelinkUEInformationNR_r16_IEs__list__Format : seq_type t_Format

val sidelinkUEInformationNR_r16_IEs__F1 :
  sidelinkUEInformationNR_r16_IEs__Type -> sL_InterestedFreqList_r16__Type
  option * (sL_TxResourceReqList_r16__Type option * (sL_FailureList_r16__Type
  option * (octet_string option * (sidelinkUEInformationNR_v1700_IEs__Type
  option * unit))))

val sidelinkUEInformationNR_r16_IEs__F2 :
  seq_type -> sidelinkUEInformationNR_r16_IEs__Type

val sidelinkUEInformationNR_r16_IEs__Format :
  sidelinkUEInformationNR_r16_IEs__Type t_Format

type sidelinkUEInformationNR_r16__criticalExtensions__criticalExtensionsFuture__Type =
| Make__SidelinkUEInformationNR_r16__criticalExtensions__criticalExtensionsFuture__Type

type sidelinkUEInformationNR_r16__criticalExtensions__Type =
| SidelinkUEInformationNR_r16__criticalExtensions__sidelinkUEInformationNR_r16 of 
   sidelinkUEInformationNR_r16_IEs__Type
| SidelinkUEInformationNR_r16__criticalExtensions__criticalExtensionsFuture of 
   sidelinkUEInformationNR_r16__criticalExtensions__criticalExtensionsFuture__Type

type sidelinkUEInformationNR_r16__Type = { sidelinkUEInformationNR_r16__criticalExtensions : 
                                           sidelinkUEInformationNR_r16__criticalExtensions__Type }

val sidelinkUEInformationNR_r16__list : seq_elem list

val sidelinkUEInformationNR_r16__criticalExtensions__criticalExtensionsFuture__Format :
  sidelinkUEInformationNR_r16__criticalExtensions__criticalExtensionsFuture__Type
  t_Format

val sidelinkUEInformationNR_r16__criticalExtensions__list__Format :
  (int, __) sigT t_Format

val sidelinkUEInformationNR_r16__criticalExtensions__F1 :
  sidelinkUEInformationNR_r16__criticalExtensions__Type -> choice

val sidelinkUEInformationNR_r16__criticalExtensions__F2 :
  choice -> sidelinkUEInformationNR_r16__criticalExtensions__Type

val sidelinkUEInformationNR_r16__criticalExtensions__Format :
  sidelinkUEInformationNR_r16__criticalExtensions__Type t_Format

type sidelinkUEInformationNR_r16__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val sidelinkUEInformationNR_r16__Format_list :
  sidelinkUEInformationNR_r16__Format_Type

val sidelinkUEInformationNR_r16__list__Format : seq_type t_Format

val sidelinkUEInformationNR_r16__F1 :
  sidelinkUEInformationNR_r16__Type ->
  sidelinkUEInformationNR_r16__criticalExtensions__Type * unit

val sidelinkUEInformationNR_r16__F2 :
  seq_type -> sidelinkUEInformationNR_r16__Type

val sidelinkUEInformationNR_r16__Format :
  sidelinkUEInformationNR_r16__Type t_Format

type uLInformationTransferIRAT_r16_IEs__nonCriticalExtension__Type =
| Make__ULInformationTransferIRAT_r16_IEs__nonCriticalExtension__Type

type uLInformationTransferIRAT_r16_IEs__Type = { uLInformationTransferIRAT_r16_IEs__ul_DCCH_MessageEUTRA_r16 : 
                                                 octet_string option;
                                                 uLInformationTransferIRAT_r16_IEs__lateNonCriticalExtension : 
                                                 octet_string option;
                                                 uLInformationTransferIRAT_r16_IEs__nonCriticalExtension : 
                                                 uLInformationTransferIRAT_r16_IEs__nonCriticalExtension__Type
                                                 option }

val uLInformationTransferIRAT_r16_IEs__list : seq_elem list

val uLInformationTransferIRAT_r16_IEs__nonCriticalExtension__Format :
  uLInformationTransferIRAT_r16_IEs__nonCriticalExtension__Type t_Format

type uLInformationTransferIRAT_r16_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val uLInformationTransferIRAT_r16_IEs__Format_list :
  uLInformationTransferIRAT_r16_IEs__Format_Type

val uLInformationTransferIRAT_r16_IEs__list__Format : seq_type t_Format

val uLInformationTransferIRAT_r16_IEs__F1 :
  uLInformationTransferIRAT_r16_IEs__Type -> octet_string
  option * (octet_string
  option * (uLInformationTransferIRAT_r16_IEs__nonCriticalExtension__Type
  option * unit))

val uLInformationTransferIRAT_r16_IEs__F2 :
  seq_type -> uLInformationTransferIRAT_r16_IEs__Type

val uLInformationTransferIRAT_r16_IEs__Format :
  uLInformationTransferIRAT_r16_IEs__Type t_Format

type uLInformationTransferIRAT_r16__criticalExtensions__c1__Type =
| ULInformationTransferIRAT_r16__criticalExtensions__c1__ulInformationTransferIRAT_r16 of 
   uLInformationTransferIRAT_r16_IEs__Type
| ULInformationTransferIRAT_r16__criticalExtensions__c1__spare3 of unit
| ULInformationTransferIRAT_r16__criticalExtensions__c1__spare2 of unit
| ULInformationTransferIRAT_r16__criticalExtensions__c1__spare1 of unit

type uLInformationTransferIRAT_r16__criticalExtensions__criticalExtensionsFuture__Type =
| Make__ULInformationTransferIRAT_r16__criticalExtensions__criticalExtensionsFuture__Type

type uLInformationTransferIRAT_r16__criticalExtensions__Type =
| ULInformationTransferIRAT_r16__criticalExtensions__c1 of uLInformationTransferIRAT_r16__criticalExtensions__c1__Type
| ULInformationTransferIRAT_r16__criticalExtensions__criticalExtensionsFuture of 
   uLInformationTransferIRAT_r16__criticalExtensions__criticalExtensionsFuture__Type

type uLInformationTransferIRAT_r16__Type = { uLInformationTransferIRAT_r16__criticalExtensions : 
                                             uLInformationTransferIRAT_r16__criticalExtensions__Type }

val uLInformationTransferIRAT_r16__list : seq_elem list

val uLInformationTransferIRAT_r16__criticalExtensions__c1__list__Format :
  (int, __) sigT t_Format

val uLInformationTransferIRAT_r16__criticalExtensions__c1__F1 :
  uLInformationTransferIRAT_r16__criticalExtensions__c1__Type -> choice

val uLInformationTransferIRAT_r16__criticalExtensions__c1__F2 :
  choice -> uLInformationTransferIRAT_r16__criticalExtensions__c1__Type

val uLInformationTransferIRAT_r16__criticalExtensions__c1__Format :
  uLInformationTransferIRAT_r16__criticalExtensions__c1__Type t_Format

val uLInformationTransferIRAT_r16__criticalExtensions__criticalExtensionsFuture__Format :
  uLInformationTransferIRAT_r16__criticalExtensions__criticalExtensionsFuture__Type
  t_Format

val uLInformationTransferIRAT_r16__criticalExtensions__list__Format :
  (int, __) sigT t_Format

val uLInformationTransferIRAT_r16__criticalExtensions__F1 :
  uLInformationTransferIRAT_r16__criticalExtensions__Type -> choice

val uLInformationTransferIRAT_r16__criticalExtensions__F2 :
  choice -> uLInformationTransferIRAT_r16__criticalExtensions__Type

val uLInformationTransferIRAT_r16__criticalExtensions__Format :
  uLInformationTransferIRAT_r16__criticalExtensions__Type t_Format

type uLInformationTransferIRAT_r16__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val uLInformationTransferIRAT_r16__Format_list :
  uLInformationTransferIRAT_r16__Format_Type

val uLInformationTransferIRAT_r16__list__Format : seq_type t_Format

val uLInformationTransferIRAT_r16__F1 :
  uLInformationTransferIRAT_r16__Type ->
  uLInformationTransferIRAT_r16__criticalExtensions__Type * unit

val uLInformationTransferIRAT_r16__F2 :
  seq_type -> uLInformationTransferIRAT_r16__Type

val uLInformationTransferIRAT_r16__Format :
  uLInformationTransferIRAT_r16__Type t_Format

type iAB_IP_AddressNumReq_r16__Type = { iAB_IP_AddressNumReq_r16__all_Traffic_NumReq_r16 : 
                                        int option;
                                        iAB_IP_AddressNumReq_r16__f1_C_Traffic_NumReq_r16 : 
                                        int option;
                                        iAB_IP_AddressNumReq_r16__f1_U_Traffic_NumReq_r16 : 
                                        int option;
                                        iAB_IP_AddressNumReq_r16__non_F1_Traffic_NumReq_r16 : 
                                        int option }

val iAB_IP_AddressNumReq_r16__root_list : seq_elem list

val iAB_IP_AddressNumReq_r16__ext_list : typ list

val iAB_IP_AddressNumReq_r16__all_Traffic_NumReq_r16__Format : int t_Format

val iAB_IP_AddressNumReq_r16__f1_C_Traffic_NumReq_r16__Format : int t_Format

val iAB_IP_AddressNumReq_r16__f1_U_Traffic_NumReq_r16__Format : int t_Format

val iAB_IP_AddressNumReq_r16__non_F1_Traffic_NumReq_r16__Format : int t_Format

type iAB_IP_AddressNumReq_r16__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

val iAB_IP_AddressNumReq_r16__root_Format_list :
  iAB_IP_AddressNumReq_r16__root_Format_Type

type iAB_IP_AddressNumReq_r16__ext_Format_Type = unit t_Format

val iAB_IP_AddressNumReq_r16__ext_Format_list :
  iAB_IP_AddressNumReq_r16__ext_Format_Type

type iAB_IP_AddressNumReq_r16__list_type = seq_type * seq_ext_type

val iAB_IP_AddressNumReq_r16__list_format :
  iAB_IP_AddressNumReq_r16__list_type t_Format

val iAB_IP_AddressNumReq_r16__F1 :
  iAB_IP_AddressNumReq_r16__Type -> iAB_IP_AddressNumReq_r16__list_type

val iAB_IP_AddressNumReq_r16__F2 :
  iAB_IP_AddressNumReq_r16__list_type -> iAB_IP_AddressNumReq_r16__Type

val iAB_IP_AddressNumReq_r16__Format : iAB_IP_AddressNumReq_r16__Type t_Format

type iAB_IP_AddressPrefixReq_r16__all_Traffic_PrefixReq_r16__Type =
| IAB_IP_AddressPrefixReq_r16__all_Traffic_PrefixReq_r16__true

val iAB_IP_AddressPrefixReq_r16__all_Traffic_PrefixReq_r16__nat__Format :
  int t_Format

val iAB_IP_AddressPrefixReq_r16__all_Traffic_PrefixReq_r16__F1 :
  iAB_IP_AddressPrefixReq_r16__all_Traffic_PrefixReq_r16__Type -> int

val iAB_IP_AddressPrefixReq_r16__all_Traffic_PrefixReq_r16__F2 :
  int -> iAB_IP_AddressPrefixReq_r16__all_Traffic_PrefixReq_r16__Type

type iAB_IP_AddressPrefixReq_r16__f1_C_Traffic_PrefixReq_r16__Type =
| IAB_IP_AddressPrefixReq_r16__f1_C_Traffic_PrefixReq_r16__true

val iAB_IP_AddressPrefixReq_r16__f1_C_Traffic_PrefixReq_r16__nat__Format :
  int t_Format

val iAB_IP_AddressPrefixReq_r16__f1_C_Traffic_PrefixReq_r16__F1 :
  iAB_IP_AddressPrefixReq_r16__f1_C_Traffic_PrefixReq_r16__Type -> int

val iAB_IP_AddressPrefixReq_r16__f1_C_Traffic_PrefixReq_r16__F2 :
  int -> iAB_IP_AddressPrefixReq_r16__f1_C_Traffic_PrefixReq_r16__Type

type iAB_IP_AddressPrefixReq_r16__f1_U_Traffic_PrefixReq_r16__Type =
| IAB_IP_AddressPrefixReq_r16__f1_U_Traffic_PrefixReq_r16__true

val iAB_IP_AddressPrefixReq_r16__f1_U_Traffic_PrefixReq_r16__nat__Format :
  int t_Format

val iAB_IP_AddressPrefixReq_r16__f1_U_Traffic_PrefixReq_r16__F1 :
  iAB_IP_AddressPrefixReq_r16__f1_U_Traffic_PrefixReq_r16__Type -> int

val iAB_IP_AddressPrefixReq_r16__f1_U_Traffic_PrefixReq_r16__F2 :
  int -> iAB_IP_AddressPrefixReq_r16__f1_U_Traffic_PrefixReq_r16__Type

type iAB_IP_AddressPrefixReq_r16__non_F1_Traffic_PrefixReq_r16__Type =
| IAB_IP_AddressPrefixReq_r16__non_F1_Traffic_PrefixReq_r16__true

val iAB_IP_AddressPrefixReq_r16__non_F1_Traffic_PrefixReq_r16__nat__Format :
  int t_Format

val iAB_IP_AddressPrefixReq_r16__non_F1_Traffic_PrefixReq_r16__F1 :
  iAB_IP_AddressPrefixReq_r16__non_F1_Traffic_PrefixReq_r16__Type -> int

val iAB_IP_AddressPrefixReq_r16__non_F1_Traffic_PrefixReq_r16__F2 :
  int -> iAB_IP_AddressPrefixReq_r16__non_F1_Traffic_PrefixReq_r16__Type

type iAB_IP_AddressPrefixReq_r16__Type = { iAB_IP_AddressPrefixReq_r16__all_Traffic_PrefixReq_r16 : 
                                           iAB_IP_AddressPrefixReq_r16__all_Traffic_PrefixReq_r16__Type
                                           option;
                                           iAB_IP_AddressPrefixReq_r16__f1_C_Traffic_PrefixReq_r16 : 
                                           iAB_IP_AddressPrefixReq_r16__f1_C_Traffic_PrefixReq_r16__Type
                                           option;
                                           iAB_IP_AddressPrefixReq_r16__f1_U_Traffic_PrefixReq_r16 : 
                                           iAB_IP_AddressPrefixReq_r16__f1_U_Traffic_PrefixReq_r16__Type
                                           option;
                                           iAB_IP_AddressPrefixReq_r16__non_F1_Traffic_PrefixReq_r16 : 
                                           iAB_IP_AddressPrefixReq_r16__non_F1_Traffic_PrefixReq_r16__Type
                                           option }

val iAB_IP_AddressPrefixReq_r16__root_list : seq_elem list

val iAB_IP_AddressPrefixReq_r16__ext_list : typ list

val iAB_IP_AddressPrefixReq_r16__all_Traffic_PrefixReq_r16__Format :
  iAB_IP_AddressPrefixReq_r16__all_Traffic_PrefixReq_r16__Type t_Format

val iAB_IP_AddressPrefixReq_r16__f1_C_Traffic_PrefixReq_r16__Format :
  iAB_IP_AddressPrefixReq_r16__f1_C_Traffic_PrefixReq_r16__Type t_Format

val iAB_IP_AddressPrefixReq_r16__f1_U_Traffic_PrefixReq_r16__Format :
  iAB_IP_AddressPrefixReq_r16__f1_U_Traffic_PrefixReq_r16__Type t_Format

val iAB_IP_AddressPrefixReq_r16__non_F1_Traffic_PrefixReq_r16__Format :
  iAB_IP_AddressPrefixReq_r16__non_F1_Traffic_PrefixReq_r16__Type t_Format

type iAB_IP_AddressPrefixReq_r16__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

val iAB_IP_AddressPrefixReq_r16__root_Format_list :
  iAB_IP_AddressPrefixReq_r16__root_Format_Type

type iAB_IP_AddressPrefixReq_r16__ext_Format_Type = unit t_Format

val iAB_IP_AddressPrefixReq_r16__ext_Format_list :
  iAB_IP_AddressPrefixReq_r16__ext_Format_Type

type iAB_IP_AddressPrefixReq_r16__list_type = seq_type * seq_ext_type

val iAB_IP_AddressPrefixReq_r16__list_format :
  iAB_IP_AddressPrefixReq_r16__list_type t_Format

val iAB_IP_AddressPrefixReq_r16__F1 :
  iAB_IP_AddressPrefixReq_r16__Type -> iAB_IP_AddressPrefixReq_r16__list_type

val iAB_IP_AddressPrefixReq_r16__F2 :
  iAB_IP_AddressPrefixReq_r16__list_type -> iAB_IP_AddressPrefixReq_r16__Type

val iAB_IP_AddressPrefixReq_r16__Format :
  iAB_IP_AddressPrefixReq_r16__Type t_Format

type iAB_IP_Address_r16__root__iPv4_Address_r16__Type = bit_string_fixed

type iAB_IP_Address_r16__root__iPv6_Address_r16__Type = bit_string_fixed

type iAB_IP_Address_r16__root__iPv6_Prefix_r16__Type = bit_string_fixed

type iAB_IP_Address_r16__root__Type =
| IAB_IP_Address_r16__root__iPv4_Address_r16 of iAB_IP_Address_r16__root__iPv4_Address_r16__Type
| IAB_IP_Address_r16__root__iPv6_Address_r16 of iAB_IP_Address_r16__root__iPv6_Address_r16__Type
| IAB_IP_Address_r16__root__iPv6_Prefix_r16 of iAB_IP_Address_r16__root__iPv6_Prefix_r16__Type

type iAB_IP_Address_r16__ext__Type = empty_set

type iAB_IP_Address_r16__Type =
  (iAB_IP_Address_r16__root__Type, iAB_IP_Address_r16__ext__Type) sum

val iAB_IP_Address_r16__root__iPv4_Address_r16__Format :
  iAB_IP_Address_r16__root__iPv4_Address_r16__Type t_Format

val iAB_IP_Address_r16__root__iPv6_Address_r16__Format :
  iAB_IP_Address_r16__root__iPv6_Address_r16__Type t_Format

val iAB_IP_Address_r16__root__iPv6_Prefix_r16__Format :
  iAB_IP_Address_r16__root__iPv6_Prefix_r16__Type t_Format

val iAB_IP_Address_r16__root__list__Format : (int, __) sigT t_Format

val iAB_IP_Address_r16__root__F1 : iAB_IP_Address_r16__root__Type -> choice

val iAB_IP_Address_r16__root__F2 : choice -> iAB_IP_Address_r16__root__Type

val iAB_IP_Address_r16__root__Format : iAB_IP_Address_r16__root__Type t_Format

val iAB_IP_Address_r16__ext__Format : iAB_IP_Address_r16__ext__Type t_Format

val iAB_IP_Address_r16__Format : iAB_IP_Address_r16__Type t_Format

type iAB_IP_AddressAndTraffic_r16__all_Traffic_IAB_IP_Address_r16__Type =
  iAB_IP_Address_r16__Type list

type iAB_IP_AddressAndTraffic_r16__f1_C_Traffic_IP_Address_r16__Type =
  iAB_IP_Address_r16__Type list

type iAB_IP_AddressAndTraffic_r16__f1_U_Traffic_IP_Address_r16__Type =
  iAB_IP_Address_r16__Type list

type iAB_IP_AddressAndTraffic_r16__non_F1_Traffic_IP_Address_r16__Type =
  iAB_IP_Address_r16__Type list

type iAB_IP_AddressAndTraffic_r16__Type = { iAB_IP_AddressAndTraffic_r16__all_Traffic_IAB_IP_Address_r16 : 
                                            iAB_IP_AddressAndTraffic_r16__all_Traffic_IAB_IP_Address_r16__Type
                                            option;
                                            iAB_IP_AddressAndTraffic_r16__f1_C_Traffic_IP_Address_r16 : 
                                            iAB_IP_AddressAndTraffic_r16__f1_C_Traffic_IP_Address_r16__Type
                                            option;
                                            iAB_IP_AddressAndTraffic_r16__f1_U_Traffic_IP_Address_r16 : 
                                            iAB_IP_AddressAndTraffic_r16__f1_U_Traffic_IP_Address_r16__Type
                                            option;
                                            iAB_IP_AddressAndTraffic_r16__non_F1_Traffic_IP_Address_r16 : 
                                            iAB_IP_AddressAndTraffic_r16__non_F1_Traffic_IP_Address_r16__Type
                                            option }

val iAB_IP_AddressAndTraffic_r16__list : seq_elem list

val iAB_IP_AddressAndTraffic_r16__all_Traffic_IAB_IP_Address_r16__Format :
  iAB_IP_AddressAndTraffic_r16__all_Traffic_IAB_IP_Address_r16__Type t_Format

val iAB_IP_AddressAndTraffic_r16__f1_C_Traffic_IP_Address_r16__Format :
  iAB_IP_AddressAndTraffic_r16__f1_C_Traffic_IP_Address_r16__Type t_Format

val iAB_IP_AddressAndTraffic_r16__f1_U_Traffic_IP_Address_r16__Format :
  iAB_IP_AddressAndTraffic_r16__f1_U_Traffic_IP_Address_r16__Type t_Format

val iAB_IP_AddressAndTraffic_r16__non_F1_Traffic_IP_Address_r16__Format :
  iAB_IP_AddressAndTraffic_r16__non_F1_Traffic_IP_Address_r16__Type t_Format

type iAB_IP_AddressAndTraffic_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

val iAB_IP_AddressAndTraffic_r16__Format_list :
  iAB_IP_AddressAndTraffic_r16__Format_Type

val iAB_IP_AddressAndTraffic_r16__list__Format : seq_type t_Format

val iAB_IP_AddressAndTraffic_r16__F1 :
  iAB_IP_AddressAndTraffic_r16__Type ->
  iAB_IP_AddressAndTraffic_r16__all_Traffic_IAB_IP_Address_r16__Type
  option * (iAB_IP_AddressAndTraffic_r16__f1_C_Traffic_IP_Address_r16__Type
  option * (iAB_IP_AddressAndTraffic_r16__f1_U_Traffic_IP_Address_r16__Type
  option * (iAB_IP_AddressAndTraffic_r16__non_F1_Traffic_IP_Address_r16__Type
  option * unit)))

val iAB_IP_AddressAndTraffic_r16__F2 :
  seq_type -> iAB_IP_AddressAndTraffic_r16__Type

val iAB_IP_AddressAndTraffic_r16__Format :
  iAB_IP_AddressAndTraffic_r16__Type t_Format

type iAB_IP_PrefixAndTraffic_r16__Type = { iAB_IP_PrefixAndTraffic_r16__all_Traffic_IAB_IP_Address_r16 : 
                                           iAB_IP_Address_r16__Type option;
                                           iAB_IP_PrefixAndTraffic_r16__f1_C_Traffic_IP_Address_r16 : 
                                           iAB_IP_Address_r16__Type option;
                                           iAB_IP_PrefixAndTraffic_r16__f1_U_Traffic_IP_Address_r16 : 
                                           iAB_IP_Address_r16__Type option;
                                           iAB_IP_PrefixAndTraffic_r16__non_F1_Traffic_IP_Address_r16 : 
                                           iAB_IP_Address_r16__Type option }

val iAB_IP_PrefixAndTraffic_r16__list : seq_elem list

type iAB_IP_PrefixAndTraffic_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

val iAB_IP_PrefixAndTraffic_r16__Format_list :
  iAB_IP_PrefixAndTraffic_r16__Format_Type

val iAB_IP_PrefixAndTraffic_r16__list__Format : seq_type t_Format

val iAB_IP_PrefixAndTraffic_r16__F1 :
  iAB_IP_PrefixAndTraffic_r16__Type -> iAB_IP_Address_r16__Type
  option * (iAB_IP_Address_r16__Type option * (iAB_IP_Address_r16__Type
  option * (iAB_IP_Address_r16__Type option * unit)))

val iAB_IP_PrefixAndTraffic_r16__F2 :
  seq_type -> iAB_IP_PrefixAndTraffic_r16__Type

val iAB_IP_PrefixAndTraffic_r16__Format :
  iAB_IP_PrefixAndTraffic_r16__Type t_Format

type iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Request_r16__iab_IPv6_AddressReq_r16__root__Type =
| IABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Request_r16__iab_IPv6_AddressReq_r16__root__iab_IPv6_AddressNumReq_r16 of 
   iAB_IP_AddressNumReq_r16__Type
| IABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Request_r16__iab_IPv6_AddressReq_r16__root__iab_IPv6_AddressPrefixReq_r16 of 
   iAB_IP_AddressPrefixReq_r16__Type

type iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Request_r16__iab_IPv6_AddressReq_r16__ext__Type =
  empty_set

type iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Request_r16__iab_IPv6_AddressReq_r16__Type =
  (iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Request_r16__iab_IPv6_AddressReq_r16__root__Type,
  iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Request_r16__iab_IPv6_AddressReq_r16__ext__Type)
  sum

type iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Request_r16__Type = { 
iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Request_r16__iab_IPv4_AddressNumReq_r16 : 
iAB_IP_AddressNumReq_r16__Type option;
iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Request_r16__iab_IPv6_AddressReq_r16 : 
iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Request_r16__iab_IPv6_AddressReq_r16__Type
option }

val iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Request_r16__list :
  seq_elem list

type iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Report_r16__iab_IPv6_Report_r16__root__Type =
| IABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Report_r16__iab_IPv6_Report_r16__root__iab_IPv6_AddressReport_r16 of 
   iAB_IP_AddressAndTraffic_r16__Type
| IABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Report_r16__iab_IPv6_Report_r16__root__iab_IPv6_PrefixReport_r16 of 
   iAB_IP_PrefixAndTraffic_r16__Type

type iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Report_r16__iab_IPv6_Report_r16__ext__Type =
  empty_set

type iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Report_r16__iab_IPv6_Report_r16__Type =
  (iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Report_r16__iab_IPv6_Report_r16__root__Type,
  iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Report_r16__iab_IPv6_Report_r16__ext__Type)
  sum

type iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Report_r16__Type = { 
iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Report_r16__iab_IPv4_AddressReport_r16 : 
iAB_IP_AddressAndTraffic_r16__Type option;
iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Report_r16__iab_IPv6_Report_r16 : 
iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Report_r16__iab_IPv6_Report_r16__Type
option }

val iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Report_r16__list :
  seq_elem list

type iABOtherInformation_r16_IEs__ip_InfoType_r16__root__Type =
| IABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Request_r16 of 
   iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Request_r16__Type
| IABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Report_r16 of 
   iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Report_r16__Type

type iABOtherInformation_r16_IEs__ip_InfoType_r16__ext__Type = empty_set

type iABOtherInformation_r16_IEs__ip_InfoType_r16__Type =
  (iABOtherInformation_r16_IEs__ip_InfoType_r16__root__Type,
  iABOtherInformation_r16_IEs__ip_InfoType_r16__ext__Type) sum

type iABOtherInformation_r16_IEs__nonCriticalExtension__Type =
| Make__IABOtherInformation_r16_IEs__nonCriticalExtension__Type

type iABOtherInformation_r16_IEs__Type = { iABOtherInformation_r16_IEs__ip_InfoType_r16 : 
                                           iABOtherInformation_r16_IEs__ip_InfoType_r16__Type;
                                           iABOtherInformation_r16_IEs__lateNonCriticalExtension : 
                                           octet_string option;
                                           iABOtherInformation_r16_IEs__nonCriticalExtension : 
                                           iABOtherInformation_r16_IEs__nonCriticalExtension__Type
                                           option }

val iABOtherInformation_r16_IEs__list : seq_elem list

val iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Request_r16__iab_IPv6_AddressReq_r16__root__list__Format :
  (int, __) sigT t_Format

val iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Request_r16__iab_IPv6_AddressReq_r16__root__F1 :
  iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Request_r16__iab_IPv6_AddressReq_r16__root__Type
  -> choice

val iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Request_r16__iab_IPv6_AddressReq_r16__root__F2 :
  choice ->
  iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Request_r16__iab_IPv6_AddressReq_r16__root__Type

val iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Request_r16__iab_IPv6_AddressReq_r16__root__Format :
  iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Request_r16__iab_IPv6_AddressReq_r16__root__Type
  t_Format

val iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Request_r16__iab_IPv6_AddressReq_r16__ext__Format :
  iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Request_r16__iab_IPv6_AddressReq_r16__ext__Type
  t_Format

val iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Request_r16__iab_IPv6_AddressReq_r16__Format :
  iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Request_r16__iab_IPv6_AddressReq_r16__Type
  t_Format

type iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Request_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Request_r16__Format_list :
  iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Request_r16__Format_Type

val iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Request_r16__list__Format :
  seq_type t_Format

val iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Request_r16__F1 :
  iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Request_r16__Type
  -> iAB_IP_AddressNumReq_r16__Type
  option * (iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Request_r16__iab_IPv6_AddressReq_r16__Type
  option * unit)

val iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Request_r16__F2 :
  seq_type ->
  iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Request_r16__Type

val iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Request_r16__Format :
  iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Request_r16__Type
  t_Format

val iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Report_r16__iab_IPv6_Report_r16__root__list__Format :
  (int, __) sigT t_Format

val iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Report_r16__iab_IPv6_Report_r16__root__F1 :
  iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Report_r16__iab_IPv6_Report_r16__root__Type
  -> choice

val iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Report_r16__iab_IPv6_Report_r16__root__F2 :
  choice ->
  iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Report_r16__iab_IPv6_Report_r16__root__Type

val iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Report_r16__iab_IPv6_Report_r16__root__Format :
  iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Report_r16__iab_IPv6_Report_r16__root__Type
  t_Format

val iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Report_r16__iab_IPv6_Report_r16__ext__Format :
  iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Report_r16__iab_IPv6_Report_r16__ext__Type
  t_Format

val iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Report_r16__iab_IPv6_Report_r16__Format :
  iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Report_r16__iab_IPv6_Report_r16__Type
  t_Format

type iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Report_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Report_r16__Format_list :
  iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Report_r16__Format_Type

val iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Report_r16__list__Format :
  seq_type t_Format

val iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Report_r16__F1 :
  iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Report_r16__Type
  -> iAB_IP_AddressAndTraffic_r16__Type
  option * (iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Report_r16__iab_IPv6_Report_r16__Type
  option * unit)

val iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Report_r16__F2 :
  seq_type ->
  iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Report_r16__Type

val iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Report_r16__Format :
  iABOtherInformation_r16_IEs__ip_InfoType_r16__root__iab_IP_Report_r16__Type
  t_Format

val iABOtherInformation_r16_IEs__ip_InfoType_r16__root__list__Format :
  (int, __) sigT t_Format

val iABOtherInformation_r16_IEs__ip_InfoType_r16__root__F1 :
  iABOtherInformation_r16_IEs__ip_InfoType_r16__root__Type -> choice

val iABOtherInformation_r16_IEs__ip_InfoType_r16__root__F2 :
  choice -> iABOtherInformation_r16_IEs__ip_InfoType_r16__root__Type

val iABOtherInformation_r16_IEs__ip_InfoType_r16__root__Format :
  iABOtherInformation_r16_IEs__ip_InfoType_r16__root__Type t_Format

val iABOtherInformation_r16_IEs__ip_InfoType_r16__ext__Format :
  iABOtherInformation_r16_IEs__ip_InfoType_r16__ext__Type t_Format

val iABOtherInformation_r16_IEs__ip_InfoType_r16__Format :
  iABOtherInformation_r16_IEs__ip_InfoType_r16__Type t_Format

val iABOtherInformation_r16_IEs__nonCriticalExtension__Format :
  iABOtherInformation_r16_IEs__nonCriticalExtension__Type t_Format

type iABOtherInformation_r16_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val iABOtherInformation_r16_IEs__Format_list :
  iABOtherInformation_r16_IEs__Format_Type

val iABOtherInformation_r16_IEs__list__Format : seq_type t_Format

val iABOtherInformation_r16_IEs__F1 :
  iABOtherInformation_r16_IEs__Type ->
  iABOtherInformation_r16_IEs__ip_InfoType_r16__Type * (octet_string
  option * (iABOtherInformation_r16_IEs__nonCriticalExtension__Type
  option * unit))

val iABOtherInformation_r16_IEs__F2 :
  seq_type -> iABOtherInformation_r16_IEs__Type

val iABOtherInformation_r16_IEs__Format :
  iABOtherInformation_r16_IEs__Type t_Format

type iABOtherInformation_r16__criticalExtensions__criticalExtensionsFuture__Type =
| Make__IABOtherInformation_r16__criticalExtensions__criticalExtensionsFuture__Type

type iABOtherInformation_r16__criticalExtensions__Type =
| IABOtherInformation_r16__criticalExtensions__iabOtherInformation_r16 of 
   iABOtherInformation_r16_IEs__Type
| IABOtherInformation_r16__criticalExtensions__criticalExtensionsFuture of 
   iABOtherInformation_r16__criticalExtensions__criticalExtensionsFuture__Type

type iABOtherInformation_r16__Type = { iABOtherInformation_r16__rrc_TransactionIdentifier : 
                                       rRC_TransactionIdentifier__Type;
                                       iABOtherInformation_r16__criticalExtensions : 
                                       iABOtherInformation_r16__criticalExtensions__Type }

val iABOtherInformation_r16__list : seq_elem list

val iABOtherInformation_r16__criticalExtensions__criticalExtensionsFuture__Format :
  iABOtherInformation_r16__criticalExtensions__criticalExtensionsFuture__Type
  t_Format

val iABOtherInformation_r16__criticalExtensions__list__Format :
  (int, __) sigT t_Format

val iABOtherInformation_r16__criticalExtensions__F1 :
  iABOtherInformation_r16__criticalExtensions__Type -> choice

val iABOtherInformation_r16__criticalExtensions__F2 :
  choice -> iABOtherInformation_r16__criticalExtensions__Type

val iABOtherInformation_r16__criticalExtensions__Format :
  iABOtherInformation_r16__criticalExtensions__Type t_Format

type iABOtherInformation_r16__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val iABOtherInformation_r16__Format_list : iABOtherInformation_r16__Format_Type

val iABOtherInformation_r16__list__Format : seq_type t_Format

val iABOtherInformation_r16__F1 :
  iABOtherInformation_r16__Type ->
  rRC_TransactionIdentifier__Type * (iABOtherInformation_r16__criticalExtensions__Type * unit)

val iABOtherInformation_r16__F2 : seq_type -> iABOtherInformation_r16__Type

val iABOtherInformation_r16__Format : iABOtherInformation_r16__Type t_Format

type carrierFreqListMBS_r17__Type = aRFCN_ValueNR__Type list

val carrierFreqListMBS_r17__Format : carrierFreqListMBS_r17__Type t_Format

type tMGI_r17__plmn_Id_r17__Type =
| TMGI_r17__plmn_Id_r17__plmn_Index of int
| TMGI_r17__plmn_Id_r17__explicitValue of pLMN_Identity__Type

type tMGI_r17__serviceId_r17__Type = octet_string

type tMGI_r17__Type = { tMGI_r17__plmn_Id_r17 : tMGI_r17__plmn_Id_r17__Type;
                        tMGI_r17__serviceId_r17 : tMGI_r17__serviceId_r17__Type }

val tMGI_r17__list : seq_elem list

val tMGI_r17__plmn_Id_r17__plmn_Index__Format : int t_Format

val tMGI_r17__plmn_Id_r17__list__Format : (int, __) sigT t_Format

val tMGI_r17__plmn_Id_r17__F1 : tMGI_r17__plmn_Id_r17__Type -> choice

val tMGI_r17__plmn_Id_r17__F2 : choice -> tMGI_r17__plmn_Id_r17__Type

val tMGI_r17__plmn_Id_r17__Format : tMGI_r17__plmn_Id_r17__Type t_Format

val tMGI_r17__serviceId_r17__Format : tMGI_r17__serviceId_r17__Type t_Format

type tMGI_r17__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val tMGI_r17__Format_list : tMGI_r17__Format_Type

val tMGI_r17__list__Format : seq_type t_Format

val tMGI_r17__F1 :
  tMGI_r17__Type ->
  tMGI_r17__plmn_Id_r17__Type * (tMGI_r17__serviceId_r17__Type * unit)

val tMGI_r17__F2 : seq_type -> tMGI_r17__Type

val tMGI_r17__Format : tMGI_r17__Type t_Format

type mBS_ServiceInfo_r17__Type = { mBS_ServiceInfo_r17__tmgi_r17 : tMGI_r17__Type }

val mBS_ServiceInfo_r17__list : seq_elem list

type mBS_ServiceInfo_r17__Format_Type = seq_elem_to_format * seq_elem_to_format

val mBS_ServiceInfo_r17__Format_list : mBS_ServiceInfo_r17__Format_Type

val mBS_ServiceInfo_r17__list__Format : seq_type t_Format

val mBS_ServiceInfo_r17__F1 :
  mBS_ServiceInfo_r17__Type -> tMGI_r17__Type * unit

val mBS_ServiceInfo_r17__F2 : seq_type -> mBS_ServiceInfo_r17__Type

val mBS_ServiceInfo_r17__Format : mBS_ServiceInfo_r17__Type t_Format

type mBS_ServiceList_r17__Type = mBS_ServiceInfo_r17__Type list

val mBS_ServiceList_r17__Format : mBS_ServiceList_r17__Type t_Format

type mBSInterestIndication_r17_IEs__mbs_Priority_r17__Type =
| MBSInterestIndication_r17_IEs__mbs_Priority_r17__true

val mBSInterestIndication_r17_IEs__mbs_Priority_r17__nat__Format : int t_Format

val mBSInterestIndication_r17_IEs__mbs_Priority_r17__F1 :
  mBSInterestIndication_r17_IEs__mbs_Priority_r17__Type -> int

val mBSInterestIndication_r17_IEs__mbs_Priority_r17__F2 :
  int -> mBSInterestIndication_r17_IEs__mbs_Priority_r17__Type

type mBSInterestIndication_r17_IEs__nonCriticalExtension__Type =
| Make__MBSInterestIndication_r17_IEs__nonCriticalExtension__Type

type mBSInterestIndication_r17_IEs__Type = { mBSInterestIndication_r17_IEs__mbs_FreqList_r17 : 
                                             carrierFreqListMBS_r17__Type
                                             option;
                                             mBSInterestIndication_r17_IEs__mbs_Priority_r17 : 
                                             mBSInterestIndication_r17_IEs__mbs_Priority_r17__Type
                                             option;
                                             mBSInterestIndication_r17_IEs__mbs_ServiceList_r17 : 
                                             mBS_ServiceList_r17__Type option;
                                             mBSInterestIndication_r17_IEs__lateNonCriticalExtension : 
                                             octet_string option;
                                             mBSInterestIndication_r17_IEs__nonCriticalExtension : 
                                             mBSInterestIndication_r17_IEs__nonCriticalExtension__Type
                                             option }

val mBSInterestIndication_r17_IEs__list : seq_elem list

val mBSInterestIndication_r17_IEs__mbs_Priority_r17__Format :
  mBSInterestIndication_r17_IEs__mbs_Priority_r17__Type t_Format

val mBSInterestIndication_r17_IEs__nonCriticalExtension__Format :
  mBSInterestIndication_r17_IEs__nonCriticalExtension__Type t_Format

type mBSInterestIndication_r17_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))))

val mBSInterestIndication_r17_IEs__Format_list :
  mBSInterestIndication_r17_IEs__Format_Type

val mBSInterestIndication_r17_IEs__list__Format : seq_type t_Format

val mBSInterestIndication_r17_IEs__F1 :
  mBSInterestIndication_r17_IEs__Type -> carrierFreqListMBS_r17__Type
  option * (mBSInterestIndication_r17_IEs__mbs_Priority_r17__Type
  option * (mBS_ServiceList_r17__Type option * (octet_string
  option * (mBSInterestIndication_r17_IEs__nonCriticalExtension__Type
  option * unit))))

val mBSInterestIndication_r17_IEs__F2 :
  seq_type -> mBSInterestIndication_r17_IEs__Type

val mBSInterestIndication_r17_IEs__Format :
  mBSInterestIndication_r17_IEs__Type t_Format

type mBSInterestIndication_r17__criticalExtensions__criticalExtensionsFuture__Type =
| Make__MBSInterestIndication_r17__criticalExtensions__criticalExtensionsFuture__Type

type mBSInterestIndication_r17__criticalExtensions__Type =
| MBSInterestIndication_r17__criticalExtensions__mbsInterestIndication_r17 of 
   mBSInterestIndication_r17_IEs__Type
| MBSInterestIndication_r17__criticalExtensions__criticalExtensionsFuture of 
   mBSInterestIndication_r17__criticalExtensions__criticalExtensionsFuture__Type

type mBSInterestIndication_r17__Type = { mBSInterestIndication_r17__criticalExtensions : 
                                         mBSInterestIndication_r17__criticalExtensions__Type }

val mBSInterestIndication_r17__list : seq_elem list

val mBSInterestIndication_r17__criticalExtensions__criticalExtensionsFuture__Format :
  mBSInterestIndication_r17__criticalExtensions__criticalExtensionsFuture__Type
  t_Format

val mBSInterestIndication_r17__criticalExtensions__list__Format :
  (int, __) sigT t_Format

val mBSInterestIndication_r17__criticalExtensions__F1 :
  mBSInterestIndication_r17__criticalExtensions__Type -> choice

val mBSInterestIndication_r17__criticalExtensions__F2 :
  choice -> mBSInterestIndication_r17__criticalExtensions__Type

val mBSInterestIndication_r17__criticalExtensions__Format :
  mBSInterestIndication_r17__criticalExtensions__Type t_Format

type mBSInterestIndication_r17__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val mBSInterestIndication_r17__Format_list :
  mBSInterestIndication_r17__Format_Type

val mBSInterestIndication_r17__list__Format : seq_type t_Format

val mBSInterestIndication_r17__F1 :
  mBSInterestIndication_r17__Type ->
  mBSInterestIndication_r17__criticalExtensions__Type * unit

val mBSInterestIndication_r17__F2 : seq_type -> mBSInterestIndication_r17__Type

val mBSInterestIndication_r17__Format :
  mBSInterestIndication_r17__Type t_Format

type nR_TimeStamp_r17__nr_Slot_r17__Type =
| NR_TimeStamp_r17__nr_Slot_r17__scs15_r17 of int
| NR_TimeStamp_r17__nr_Slot_r17__scs30_r17 of int
| NR_TimeStamp_r17__nr_Slot_r17__scs60_r17 of int
| NR_TimeStamp_r17__nr_Slot_r17__scs120_r17 of int

type nR_TimeStamp_r17__Type = { nR_TimeStamp_r17__nr_SFN_r17 : int;
                                nR_TimeStamp_r17__nr_Slot_r17 : nR_TimeStamp_r17__nr_Slot_r17__Type }

val nR_TimeStamp_r17__root_list : seq_elem list

val nR_TimeStamp_r17__ext_list : typ list

val nR_TimeStamp_r17__nr_SFN_r17__Format : int t_Format

val nR_TimeStamp_r17__nr_Slot_r17__scs15_r17__Format : int t_Format

val nR_TimeStamp_r17__nr_Slot_r17__scs30_r17__Format : int t_Format

val nR_TimeStamp_r17__nr_Slot_r17__scs60_r17__Format : int t_Format

val nR_TimeStamp_r17__nr_Slot_r17__scs120_r17__Format : int t_Format

val nR_TimeStamp_r17__nr_Slot_r17__list__Format : (int, __) sigT t_Format

val nR_TimeStamp_r17__nr_Slot_r17__F1 :
  nR_TimeStamp_r17__nr_Slot_r17__Type -> choice

val nR_TimeStamp_r17__nr_Slot_r17__F2 :
  choice -> nR_TimeStamp_r17__nr_Slot_r17__Type

val nR_TimeStamp_r17__nr_Slot_r17__Format :
  nR_TimeStamp_r17__nr_Slot_r17__Type t_Format

type nR_TimeStamp_r17__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val nR_TimeStamp_r17__root_Format_list : nR_TimeStamp_r17__root_Format_Type

type nR_TimeStamp_r17__ext_Format_Type = unit t_Format

val nR_TimeStamp_r17__ext_Format_list : nR_TimeStamp_r17__ext_Format_Type

type nR_TimeStamp_r17__list_type = seq_type * seq_ext_type

val nR_TimeStamp_r17__list_format : nR_TimeStamp_r17__list_type t_Format

val nR_TimeStamp_r17__F1 :
  nR_TimeStamp_r17__Type -> nR_TimeStamp_r17__list_type

val nR_TimeStamp_r17__F2 :
  nR_TimeStamp_r17__list_type -> nR_TimeStamp_r17__Type

val nR_TimeStamp_r17__Format : nR_TimeStamp_r17__Type t_Format

type sRS_PosResourceId_r16__Type = int

val sRS_PosResourceId_r16__Format : int t_Format

type uE_TxTEG_Association_r17__associatedSRS_PosResourceIdList_r17__Type =
  sRS_PosResourceId_r16__Type list

type uE_TxTEG_Association_r17__Type = { uE_TxTEG_Association_r17__ue_TxTEG_ID_r17 : 
                                        int;
                                        uE_TxTEG_Association_r17__nr_TimeStamp_r17 : 
                                        nR_TimeStamp_r17__Type;
                                        uE_TxTEG_Association_r17__associatedSRS_PosResourceIdList_r17 : 
                                        uE_TxTEG_Association_r17__associatedSRS_PosResourceIdList_r17__Type;
                                        uE_TxTEG_Association_r17__servCellId_r17 : 
                                        servCellIndex__Type option }

val uE_TxTEG_Association_r17__list : seq_elem list

val uE_TxTEG_Association_r17__ue_TxTEG_ID_r17__Format : int t_Format

val uE_TxTEG_Association_r17__associatedSRS_PosResourceIdList_r17__Format :
  uE_TxTEG_Association_r17__associatedSRS_PosResourceIdList_r17__Type t_Format

type uE_TxTEG_Association_r17__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

val uE_TxTEG_Association_r17__Format_list :
  uE_TxTEG_Association_r17__Format_Type

val uE_TxTEG_Association_r17__list__Format : seq_type t_Format

val uE_TxTEG_Association_r17__F1 :
  uE_TxTEG_Association_r17__Type ->
  int * (nR_TimeStamp_r17__Type * (uE_TxTEG_Association_r17__associatedSRS_PosResourceIdList_r17__Type * (servCellIndex__Type
  option * unit)))

val uE_TxTEG_Association_r17__F2 : seq_type -> uE_TxTEG_Association_r17__Type

val uE_TxTEG_Association_r17__Format : uE_TxTEG_Association_r17__Type t_Format

type uE_TxTEG_AssociationList_r17__Type = uE_TxTEG_Association_r17__Type list

val uE_TxTEG_AssociationList_r17__Format :
  uE_TxTEG_AssociationList_r17__Type t_Format

type uEPositioningAssistanceInfo_v1720_IEs__ue_TxTEG_TimingErrorMarginValue_r17__Type =
| UEPositioningAssistanceInfo_v1720_IEs__ue_TxTEG_TimingErrorMarginValue_r17__tc0
| UEPositioningAssistanceInfo_v1720_IEs__ue_TxTEG_TimingErrorMarginValue_r17__tc2
| UEPositioningAssistanceInfo_v1720_IEs__ue_TxTEG_TimingErrorMarginValue_r17__tc4
| UEPositioningAssistanceInfo_v1720_IEs__ue_TxTEG_TimingErrorMarginValue_r17__tc6
| UEPositioningAssistanceInfo_v1720_IEs__ue_TxTEG_TimingErrorMarginValue_r17__tc8
| UEPositioningAssistanceInfo_v1720_IEs__ue_TxTEG_TimingErrorMarginValue_r17__tc12
| UEPositioningAssistanceInfo_v1720_IEs__ue_TxTEG_TimingErrorMarginValue_r17__tc16
| UEPositioningAssistanceInfo_v1720_IEs__ue_TxTEG_TimingErrorMarginValue_r17__tc20
| UEPositioningAssistanceInfo_v1720_IEs__ue_TxTEG_TimingErrorMarginValue_r17__tc24
| UEPositioningAssistanceInfo_v1720_IEs__ue_TxTEG_TimingErrorMarginValue_r17__tc32
| UEPositioningAssistanceInfo_v1720_IEs__ue_TxTEG_TimingErrorMarginValue_r17__tc40
| UEPositioningAssistanceInfo_v1720_IEs__ue_TxTEG_TimingErrorMarginValue_r17__tc48
| UEPositioningAssistanceInfo_v1720_IEs__ue_TxTEG_TimingErrorMarginValue_r17__tc56
| UEPositioningAssistanceInfo_v1720_IEs__ue_TxTEG_TimingErrorMarginValue_r17__tc64
| UEPositioningAssistanceInfo_v1720_IEs__ue_TxTEG_TimingErrorMarginValue_r17__tc72
| UEPositioningAssistanceInfo_v1720_IEs__ue_TxTEG_TimingErrorMarginValue_r17__tc80

val uEPositioningAssistanceInfo_v1720_IEs__ue_TxTEG_TimingErrorMarginValue_r17__nat__Format :
  int t_Format

val uEPositioningAssistanceInfo_v1720_IEs__ue_TxTEG_TimingErrorMarginValue_r17__F1 :
  uEPositioningAssistanceInfo_v1720_IEs__ue_TxTEG_TimingErrorMarginValue_r17__Type
  -> int

val uEPositioningAssistanceInfo_v1720_IEs__ue_TxTEG_TimingErrorMarginValue_r17__F2 :
  int ->
  uEPositioningAssistanceInfo_v1720_IEs__ue_TxTEG_TimingErrorMarginValue_r17__Type

type uEPositioningAssistanceInfo_v1720_IEs__nonCriticalExtension__Type =
| Make__UEPositioningAssistanceInfo_v1720_IEs__nonCriticalExtension__Type

type uEPositioningAssistanceInfo_v1720_IEs__Type = { uEPositioningAssistanceInfo_v1720_IEs__ue_TxTEG_TimingErrorMarginValue_r17 : 
                                                     uEPositioningAssistanceInfo_v1720_IEs__ue_TxTEG_TimingErrorMarginValue_r17__Type
                                                     option;
                                                     uEPositioningAssistanceInfo_v1720_IEs__nonCriticalExtension : 
                                                     uEPositioningAssistanceInfo_v1720_IEs__nonCriticalExtension__Type
                                                     option }

val uEPositioningAssistanceInfo_v1720_IEs__list : seq_elem list

val uEPositioningAssistanceInfo_v1720_IEs__ue_TxTEG_TimingErrorMarginValue_r17__Format :
  uEPositioningAssistanceInfo_v1720_IEs__ue_TxTEG_TimingErrorMarginValue_r17__Type
  t_Format

val uEPositioningAssistanceInfo_v1720_IEs__nonCriticalExtension__Format :
  uEPositioningAssistanceInfo_v1720_IEs__nonCriticalExtension__Type t_Format

type uEPositioningAssistanceInfo_v1720_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)

val uEPositioningAssistanceInfo_v1720_IEs__Format_list :
  uEPositioningAssistanceInfo_v1720_IEs__Format_Type

val uEPositioningAssistanceInfo_v1720_IEs__list__Format : seq_type t_Format

val uEPositioningAssistanceInfo_v1720_IEs__F1 :
  uEPositioningAssistanceInfo_v1720_IEs__Type ->
  uEPositioningAssistanceInfo_v1720_IEs__ue_TxTEG_TimingErrorMarginValue_r17__Type
  option * (uEPositioningAssistanceInfo_v1720_IEs__nonCriticalExtension__Type
  option * unit)

val uEPositioningAssistanceInfo_v1720_IEs__F2 :
  seq_type -> uEPositioningAssistanceInfo_v1720_IEs__Type

val uEPositioningAssistanceInfo_v1720_IEs__Format :
  uEPositioningAssistanceInfo_v1720_IEs__Type t_Format

type uEPositioningAssistanceInfo_r17_IEs__Type = { uEPositioningAssistanceInfo_r17_IEs__ue_TxTEG_AssociationList_r17 : 
                                                   uE_TxTEG_AssociationList_r17__Type
                                                   option;
                                                   uEPositioningAssistanceInfo_r17_IEs__lateNonCriticalExtension : 
                                                   octet_string option;
                                                   uEPositioningAssistanceInfo_r17_IEs__nonCriticalExtension : 
                                                   uEPositioningAssistanceInfo_v1720_IEs__Type
                                                   option }

val uEPositioningAssistanceInfo_r17_IEs__list : seq_elem list

type uEPositioningAssistanceInfo_r17_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val uEPositioningAssistanceInfo_r17_IEs__Format_list :
  uEPositioningAssistanceInfo_r17_IEs__Format_Type

val uEPositioningAssistanceInfo_r17_IEs__list__Format : seq_type t_Format

val uEPositioningAssistanceInfo_r17_IEs__F1 :
  uEPositioningAssistanceInfo_r17_IEs__Type ->
  uE_TxTEG_AssociationList_r17__Type option * (octet_string
  option * (uEPositioningAssistanceInfo_v1720_IEs__Type option * unit))

val uEPositioningAssistanceInfo_r17_IEs__F2 :
  seq_type -> uEPositioningAssistanceInfo_r17_IEs__Type

val uEPositioningAssistanceInfo_r17_IEs__Format :
  uEPositioningAssistanceInfo_r17_IEs__Type t_Format

type uEPositioningAssistanceInfo_r17__criticalExtensions__criticalExtensionsFuture__Type =
| Make__UEPositioningAssistanceInfo_r17__criticalExtensions__criticalExtensionsFuture__Type

type uEPositioningAssistanceInfo_r17__criticalExtensions__Type =
| UEPositioningAssistanceInfo_r17__criticalExtensions__uePositioningAssistanceInfo_r17 of 
   uEPositioningAssistanceInfo_r17_IEs__Type
| UEPositioningAssistanceInfo_r17__criticalExtensions__criticalExtensionsFuture of 
   uEPositioningAssistanceInfo_r17__criticalExtensions__criticalExtensionsFuture__Type

type uEPositioningAssistanceInfo_r17__Type = { uEPositioningAssistanceInfo_r17__criticalExtensions : 
                                               uEPositioningAssistanceInfo_r17__criticalExtensions__Type }

val uEPositioningAssistanceInfo_r17__list : seq_elem list

val uEPositioningAssistanceInfo_r17__criticalExtensions__criticalExtensionsFuture__Format :
  uEPositioningAssistanceInfo_r17__criticalExtensions__criticalExtensionsFuture__Type
  t_Format

val uEPositioningAssistanceInfo_r17__criticalExtensions__list__Format :
  (int, __) sigT t_Format

val uEPositioningAssistanceInfo_r17__criticalExtensions__F1 :
  uEPositioningAssistanceInfo_r17__criticalExtensions__Type -> choice

val uEPositioningAssistanceInfo_r17__criticalExtensions__F2 :
  choice -> uEPositioningAssistanceInfo_r17__criticalExtensions__Type

val uEPositioningAssistanceInfo_r17__criticalExtensions__Format :
  uEPositioningAssistanceInfo_r17__criticalExtensions__Type t_Format

type uEPositioningAssistanceInfo_r17__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val uEPositioningAssistanceInfo_r17__Format_list :
  uEPositioningAssistanceInfo_r17__Format_Type

val uEPositioningAssistanceInfo_r17__list__Format : seq_type t_Format

val uEPositioningAssistanceInfo_r17__F1 :
  uEPositioningAssistanceInfo_r17__Type ->
  uEPositioningAssistanceInfo_r17__criticalExtensions__Type * unit

val uEPositioningAssistanceInfo_r17__F2 :
  seq_type -> uEPositioningAssistanceInfo_r17__Type

val uEPositioningAssistanceInfo_r17__Format :
  uEPositioningAssistanceInfo_r17__Type t_Format

type measConfigAppLayerId_r17__Type = int

val measConfigAppLayerId_r17__Format : int t_Format

type appLayerBufferLevel_r17__Type = int

val appLayerBufferLevel_r17__Format : int t_Format

type pDU_SessionID__Type = int

val pDU_SessionID__Format : int t_Format

type rAN_VisibleMeasurements_r17__appLayerBufferLevelList_r17__Type =
  appLayerBufferLevel_r17__Type list

type rAN_VisibleMeasurements_r17__pdu_SessionIdList_r17__Type =
  pDU_SessionID__Type list

type rAN_VisibleMeasurements_r17__Type = { rAN_VisibleMeasurements_r17__appLayerBufferLevelList_r17 : 
                                           rAN_VisibleMeasurements_r17__appLayerBufferLevelList_r17__Type
                                           option;
                                           rAN_VisibleMeasurements_r17__playoutDelayForMediaStartup_r17 : 
                                           int option;
                                           rAN_VisibleMeasurements_r17__pdu_SessionIdList_r17 : 
                                           rAN_VisibleMeasurements_r17__pdu_SessionIdList_r17__Type
                                           option }

val rAN_VisibleMeasurements_r17__root_list : seq_elem list

val rAN_VisibleMeasurements_r17__ext_list : typ list

val rAN_VisibleMeasurements_r17__appLayerBufferLevelList_r17__Format :
  rAN_VisibleMeasurements_r17__appLayerBufferLevelList_r17__Type t_Format

val rAN_VisibleMeasurements_r17__playoutDelayForMediaStartup_r17__Format :
  int t_Format

val rAN_VisibleMeasurements_r17__pdu_SessionIdList_r17__Format :
  rAN_VisibleMeasurements_r17__pdu_SessionIdList_r17__Type t_Format

type rAN_VisibleMeasurements_r17__root_Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val rAN_VisibleMeasurements_r17__root_Format_list :
  rAN_VisibleMeasurements_r17__root_Format_Type

type rAN_VisibleMeasurements_r17__ext_Format_Type = unit t_Format

val rAN_VisibleMeasurements_r17__ext_Format_list :
  rAN_VisibleMeasurements_r17__ext_Format_Type

type rAN_VisibleMeasurements_r17__list_type = seq_type * seq_ext_type

val rAN_VisibleMeasurements_r17__list_format :
  rAN_VisibleMeasurements_r17__list_type t_Format

val rAN_VisibleMeasurements_r17__F1 :
  rAN_VisibleMeasurements_r17__Type -> rAN_VisibleMeasurements_r17__list_type

val rAN_VisibleMeasurements_r17__F2 :
  rAN_VisibleMeasurements_r17__list_type -> rAN_VisibleMeasurements_r17__Type

val rAN_VisibleMeasurements_r17__Format :
  rAN_VisibleMeasurements_r17__Type t_Format

type measReportAppLayer_r17__appLayerSessionStatus_r17__Type =
| MeasReportAppLayer_r17__appLayerSessionStatus_r17__started
| MeasReportAppLayer_r17__appLayerSessionStatus_r17__stopped

val measReportAppLayer_r17__appLayerSessionStatus_r17__nat__Format :
  int t_Format

val measReportAppLayer_r17__appLayerSessionStatus_r17__F1 :
  measReportAppLayer_r17__appLayerSessionStatus_r17__Type -> int

val measReportAppLayer_r17__appLayerSessionStatus_r17__F2 :
  int -> measReportAppLayer_r17__appLayerSessionStatus_r17__Type

type measReportAppLayer_r17__Type = { measReportAppLayer_r17__measConfigAppLayerId_r17 : 
                                      measConfigAppLayerId_r17__Type;
                                      measReportAppLayer_r17__measReportAppLayerContainer_r17 : 
                                      octet_string option;
                                      measReportAppLayer_r17__appLayerSessionStatus_r17 : 
                                      measReportAppLayer_r17__appLayerSessionStatus_r17__Type
                                      option;
                                      measReportAppLayer_r17__ran_VisibleMeasurements_r17 : 
                                      rAN_VisibleMeasurements_r17__Type option }

val measReportAppLayer_r17__list : seq_elem list

val measReportAppLayer_r17__appLayerSessionStatus_r17__Format :
  measReportAppLayer_r17__appLayerSessionStatus_r17__Type t_Format

type measReportAppLayer_r17__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format)))

val measReportAppLayer_r17__Format_list : measReportAppLayer_r17__Format_Type

val measReportAppLayer_r17__list__Format : seq_type t_Format

val measReportAppLayer_r17__F1 :
  measReportAppLayer_r17__Type ->
  measConfigAppLayerId_r17__Type * (octet_string
  option * (measReportAppLayer_r17__appLayerSessionStatus_r17__Type
  option * (rAN_VisibleMeasurements_r17__Type option * unit)))

val measReportAppLayer_r17__F2 : seq_type -> measReportAppLayer_r17__Type

val measReportAppLayer_r17__Format : measReportAppLayer_r17__Type t_Format

type measurementReportAppLayerList_r17__Type =
  measReportAppLayer_r17__Type list

val measurementReportAppLayerList_r17__Format :
  measurementReportAppLayerList_r17__Type t_Format

type measurementReportAppLayer_r17_IEs__nonCriticalExtension__Type =
| Make__MeasurementReportAppLayer_r17_IEs__nonCriticalExtension__Type

type measurementReportAppLayer_r17_IEs__Type = { measurementReportAppLayer_r17_IEs__measurementReportAppLayerList_r17 : 
                                                 measurementReportAppLayerList_r17__Type;
                                                 measurementReportAppLayer_r17_IEs__lateNonCriticalExtension : 
                                                 octet_string option;
                                                 measurementReportAppLayer_r17_IEs__nonCriticalExtension : 
                                                 measurementReportAppLayer_r17_IEs__nonCriticalExtension__Type
                                                 option }

val measurementReportAppLayer_r17_IEs__list : seq_elem list

val measurementReportAppLayer_r17_IEs__nonCriticalExtension__Format :
  measurementReportAppLayer_r17_IEs__nonCriticalExtension__Type t_Format

type measurementReportAppLayer_r17_IEs__Format_Type =
  seq_elem_to_format * (seq_elem_to_format * (seq_elem_to_format * seq_elem_to_format))

val measurementReportAppLayer_r17_IEs__Format_list :
  measurementReportAppLayer_r17_IEs__Format_Type

val measurementReportAppLayer_r17_IEs__list__Format : seq_type t_Format

val measurementReportAppLayer_r17_IEs__F1 :
  measurementReportAppLayer_r17_IEs__Type ->
  measurementReportAppLayerList_r17__Type * (octet_string
  option * (measurementReportAppLayer_r17_IEs__nonCriticalExtension__Type
  option * unit))

val measurementReportAppLayer_r17_IEs__F2 :
  seq_type -> measurementReportAppLayer_r17_IEs__Type

val measurementReportAppLayer_r17_IEs__Format :
  measurementReportAppLayer_r17_IEs__Type t_Format

type measurementReportAppLayer_r17__criticalExtensions__criticalExtensionsFuture__Type =
| Make__MeasurementReportAppLayer_r17__criticalExtensions__criticalExtensionsFuture__Type

type measurementReportAppLayer_r17__criticalExtensions__Type =
| MeasurementReportAppLayer_r17__criticalExtensions__measurementReportAppLayer_r17 of 
   measurementReportAppLayer_r17_IEs__Type
| MeasurementReportAppLayer_r17__criticalExtensions__criticalExtensionsFuture of 
   measurementReportAppLayer_r17__criticalExtensions__criticalExtensionsFuture__Type

type measurementReportAppLayer_r17__Type = { measurementReportAppLayer_r17__criticalExtensions : 
                                             measurementReportAppLayer_r17__criticalExtensions__Type }

val measurementReportAppLayer_r17__list : seq_elem list

val measurementReportAppLayer_r17__criticalExtensions__criticalExtensionsFuture__Format :
  measurementReportAppLayer_r17__criticalExtensions__criticalExtensionsFuture__Type
  t_Format

val measurementReportAppLayer_r17__criticalExtensions__list__Format :
  (int, __) sigT t_Format

val measurementReportAppLayer_r17__criticalExtensions__F1 :
  measurementReportAppLayer_r17__criticalExtensions__Type -> choice

val measurementReportAppLayer_r17__criticalExtensions__F2 :
  choice -> measurementReportAppLayer_r17__criticalExtensions__Type

val measurementReportAppLayer_r17__criticalExtensions__Format :
  measurementReportAppLayer_r17__criticalExtensions__Type t_Format

type measurementReportAppLayer_r17__Format_Type =
  seq_elem_to_format * seq_elem_to_format

val measurementReportAppLayer_r17__Format_list :
  measurementReportAppLayer_r17__Format_Type

val measurementReportAppLayer_r17__list__Format : seq_type t_Format

val measurementReportAppLayer_r17__F1 :
  measurementReportAppLayer_r17__Type ->
  measurementReportAppLayer_r17__criticalExtensions__Type * unit

val measurementReportAppLayer_r17__F2 :
  seq_type -> measurementReportAppLayer_r17__Type

val measurementReportAppLayer_r17__Format :
  measurementReportAppLayer_r17__Type t_Format

type uL_DCCH_MessageType__c1__Type =
| UL_DCCH_MessageType__c1__measurementReport of measurementReport__Type
| UL_DCCH_MessageType__c1__rrcReconfigurationComplete of rRCReconfigurationComplete__Type
| UL_DCCH_MessageType__c1__rrcSetupComplete of rRCSetupComplete__Type
| UL_DCCH_MessageType__c1__rrcReestablishmentComplete of rRCReestablishmentComplete__Type
| UL_DCCH_MessageType__c1__rrcResumeComplete of rRCResumeComplete__Type
| UL_DCCH_MessageType__c1__securityModeComplete of securityModeComplete__Type
| UL_DCCH_MessageType__c1__securityModeFailure of securityModeFailure__Type
| UL_DCCH_MessageType__c1__ulInformationTransfer of uLInformationTransfer__Type
| UL_DCCH_MessageType__c1__locationMeasurementIndication of locationMeasurementIndication__Type
| UL_DCCH_MessageType__c1__ueCapabilityInformation of uECapabilityInformation__Type
| UL_DCCH_MessageType__c1__counterCheckResponse of counterCheckResponse__Type
| UL_DCCH_MessageType__c1__ueAssistanceInformation of uEAssistanceInformation__Type
| UL_DCCH_MessageType__c1__failureInformation of failureInformation__Type
| UL_DCCH_MessageType__c1__ulInformationTransferMRDC of uLInformationTransferMRDC__Type
| UL_DCCH_MessageType__c1__scgFailureInformation of sCGFailureInformation__Type
| UL_DCCH_MessageType__c1__scgFailureInformationEUTRA of sCGFailureInformationEUTRA__Type

type uL_DCCH_MessageType__messageClassExtension__c2__Type =
| UL_DCCH_MessageType__messageClassExtension__c2__ulDedicatedMessageSegment_r16 of 
   uLDedicatedMessageSegment_r16__Type
| UL_DCCH_MessageType__messageClassExtension__c2__dedicatedSIBRequest_r16 of 
   dedicatedSIBRequest_r16__Type
| UL_DCCH_MessageType__messageClassExtension__c2__mcgFailureInformation_r16 of 
   mCGFailureInformation_r16__Type
| UL_DCCH_MessageType__messageClassExtension__c2__ueInformationResponse_r16 of 
   uEInformationResponse_r16__Type
| UL_DCCH_MessageType__messageClassExtension__c2__sidelinkUEInformationNR_r16 of 
   sidelinkUEInformationNR_r16__Type
| UL_DCCH_MessageType__messageClassExtension__c2__ulInformationTransferIRAT_r16 of 
   uLInformationTransferIRAT_r16__Type
| UL_DCCH_MessageType__messageClassExtension__c2__iabOtherInformation_r16 of 
   iABOtherInformation_r16__Type
| UL_DCCH_MessageType__messageClassExtension__c2__mbsInterestIndication_r17 of 
   mBSInterestIndication_r17__Type
| UL_DCCH_MessageType__messageClassExtension__c2__uePositioningAssistanceInfo_r17 of 
   uEPositioningAssistanceInfo_r17__Type
| UL_DCCH_MessageType__messageClassExtension__c2__measurementReportAppLayer_r17 of 
   measurementReportAppLayer_r17__Type
| UL_DCCH_MessageType__messageClassExtension__c2__spare6 of unit
| UL_DCCH_MessageType__messageClassExtension__c2__spare5 of unit
| UL_DCCH_MessageType__messageClassExtension__c2__spare4 of unit
| UL_DCCH_MessageType__messageClassExtension__c2__spare3 of unit
| UL_DCCH_MessageType__messageClassExtension__c2__spare2 of unit
| UL_DCCH_MessageType__messageClassExtension__c2__spare1 of unit

type uL_DCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r16__Type =
| Make__UL_DCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r16__Type

type uL_DCCH_MessageType__messageClassExtension__Type =
| UL_DCCH_MessageType__messageClassExtension__c2 of uL_DCCH_MessageType__messageClassExtension__c2__Type
| UL_DCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r16 of 
   uL_DCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r16__Type

type uL_DCCH_MessageType__Type =
| UL_DCCH_MessageType__c1 of uL_DCCH_MessageType__c1__Type
| UL_DCCH_MessageType__messageClassExtension of uL_DCCH_MessageType__messageClassExtension__Type

val uL_DCCH_MessageType__c1__list__Format : (int, __) sigT t_Format

val uL_DCCH_MessageType__c1__F1 : uL_DCCH_MessageType__c1__Type -> choice

val uL_DCCH_MessageType__c1__F2 : choice -> uL_DCCH_MessageType__c1__Type

val uL_DCCH_MessageType__c1__Format : uL_DCCH_MessageType__c1__Type t_Format

val uL_DCCH_MessageType__messageClassExtension__c2__list__Format :
  (int, __) sigT t_Format

val uL_DCCH_MessageType__messageClassExtension__c2__F1 :
  uL_DCCH_MessageType__messageClassExtension__c2__Type -> choice

val uL_DCCH_MessageType__messageClassExtension__c2__F2 :
  choice -> uL_DCCH_MessageType__messageClassExtension__c2__Type

val uL_DCCH_MessageType__messageClassExtension__c2__Format :
  uL_DCCH_MessageType__messageClassExtension__c2__Type t_Format

val uL_DCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r16__Format :
  uL_DCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r16__Type
  t_Format

val uL_DCCH_MessageType__messageClassExtension__list__Format :
  (int, __) sigT t_Format

val uL_DCCH_MessageType__messageClassExtension__F1 :
  uL_DCCH_MessageType__messageClassExtension__Type -> choice

val uL_DCCH_MessageType__messageClassExtension__F2 :
  choice -> uL_DCCH_MessageType__messageClassExtension__Type

val uL_DCCH_MessageType__messageClassExtension__Format :
  uL_DCCH_MessageType__messageClassExtension__Type t_Format

val uL_DCCH_MessageType__list__Format : (int, __) sigT t_Format

val uL_DCCH_MessageType__F1 : uL_DCCH_MessageType__Type -> choice

val uL_DCCH_MessageType__F2 : choice -> uL_DCCH_MessageType__Type

val uL_DCCH_MessageType__Format : uL_DCCH_MessageType__Type t_Format

type uL_DCCH_Message__Type = { uL_DCCH_Message__message : uL_DCCH_MessageType__Type }

val uL_DCCH_Message__list : seq_elem list

type uL_DCCH_Message__Format_Type = seq_elem_to_format * seq_elem_to_format

val uL_DCCH_Message__Format_list : uL_DCCH_Message__Format_Type

val uL_DCCH_Message__list__Format : seq_type t_Format

val uL_DCCH_Message__F1 :
  uL_DCCH_Message__Type -> uL_DCCH_MessageType__Type * unit

val uL_DCCH_Message__F2 : seq_type -> uL_DCCH_Message__Type

val uL_DCCH_Message__Format : uL_DCCH_Message__Type t_Format
