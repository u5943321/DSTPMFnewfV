structure tmsytxTheory :> tmsytxTheory =
struct
  
  val _ = if !Globals.print_thy_loads
    then TextIO.print "Loading tmsytxTheory ... "
    else ()
  
  open Type Term Thm
  local open string_numTheory in end;
  
  structure TDB = struct
    val thydata = 
      TheoryReader.load_thydata "tmsytx"
        (holpathdb.subst_pathvars "/Users/yimingxu/Documents/GitHub/DSTPMFnewfV/formalisation/tmsytxTheory.dat")
    fun find s = HOLdict.find (thydata,s)
  end
  
  fun op sort_of_def _ = () val op sort_of_def = TDB.find "sort_of_def"
  fun op foutput_def _ = () val op foutput_def = TDB.find "foutput_def"
  fun op finput_def _ = () val op finput_def = TDB.find "finput_def"
  fun op tinst_def_UNION_extract0 _ = ()
  val op tinst_def_UNION_extract0 = TDB.find "tinst_def_UNION_extract0"
  fun op tinst_def_UNION_extract1 _ = ()
  val op tinst_def_UNION_extract1 = TDB.find "tinst_def_UNION_extract1"
  fun op tinst_def_UNION_primitive _ = ()
  val op tinst_def_UNION_primitive = TDB.find "tinst_def_UNION_primitive"
  fun op tfv_def_UNION_extract0 _ = ()
  val op tfv_def_UNION_extract0 = TDB.find "tfv_def_UNION_extract0"
  fun op tfv_def_UNION_extract1 _ = ()
  val op tfv_def_UNION_extract1 = TDB.find "tfv_def_UNION_extract1"
  fun op tfv_def_UNION_primitive _ = ()
  val op tfv_def_UNION_primitive = TDB.find "tfv_def_UNION_primitive"
  fun op term_size_def _ = ()
  val op term_size_def = TDB.find "term_size_def"
  fun op sort_case_def _ = ()
  val op sort_case_def = TDB.find "sort_case_def"
  fun op term_case_def _ = ()
  val op term_case_def = TDB.find "term_case_def"
  fun op sort_TY_DEF _ = () val op sort_TY_DEF = TDB.find "sort_TY_DEF"
  fun op term_TY_DEF _ = () val op term_TY_DEF = TDB.find "term_TY_DEF"
  fun op is_cont_def _ = () val op is_cont_def = TDB.find "is_cont_def"
  fun op complete_def _ = () val op complete_def = TDB.find "complete_def"
  fun op vmap_fix_def _ = () val op vmap_fix_def = TDB.find "vmap_fix_def"
  fun op cstt_def _ = () val op cstt_def = TDB.find "cstt_def"
  fun op stms_def _ = () val op stms_def = TDB.find "stms_def"
  fun op tmatch_def_UNION_extract0 _ = ()
  val op tmatch_def_UNION_extract0 = TDB.find "tmatch_def_UNION_extract0"
  fun op tmatch_def_UNION_extract1 _ = ()
  val op tmatch_def_UNION_extract1 = TDB.find "tmatch_def_UNION_extract1"
  fun op tmatch_def_UNION_extract2 _ = ()
  val op tmatch_def_UNION_extract2 = TDB.find "tmatch_def_UNION_extract2"
  fun op tmatch_def_UNION_primitive _ = ()
  val op tmatch_def_UNION_primitive = TDB.find "tmatch_def_UNION_primitive"
  fun op tmatch_def_UNION_AUX _ = ()
  val op tmatch_def_UNION_AUX = TDB.find "tmatch_def_UNION_AUX"
  fun op no_bound_def _ = () val op no_bound_def = TDB.find "no_bound_def"
  fun op tbounds_def_UNION_extract0 _ = ()
  val op tbounds_def_UNION_extract0 = TDB.find "tbounds_def_UNION_extract0"
  fun op tbounds_def_UNION_extract1 _ = ()
  val op tbounds_def_UNION_extract1 = TDB.find "tbounds_def_UNION_extract1"
  fun op tbounds_def_UNION_primitive _ = ()
  val op tbounds_def_UNION_primitive = TDB.find
    "tbounds_def_UNION_primitive"
  fun op is_bound_def _ = () val op is_bound_def = TDB.find "is_bound_def"
  fun op o_vmap_def _ = () val op o_vmap_def = TDB.find "o_vmap_def"
  fun op tsubtm_def_UNION_primitive _ = ()
  val op tsubtm_def_UNION_primitive = TDB.find "tsubtm_def_UNION_primitive"
  fun op tsubtm_def_UNION_extract1 _ = ()
  val op tsubtm_def_UNION_extract1 = TDB.find "tsubtm_def_UNION_extract1"
  fun op tsubtm_def_UNION_extract0 _ = ()
  val op tsubtm_def_UNION_extract0 = TDB.find "tsubtm_def_UNION_extract0"
  fun op fsymin_def _ = () val op fsymin_def = TDB.find "fsymin_def"
  fun op fsymout_def _ = () val op fsymout_def = TDB.find "fsymout_def"
  fun op isfsym_def _ = () val op isfsym_def = TDB.find "isfsym_def"
  fun op wft_def_UNION_primitive _ = ()
  val op wft_def_UNION_primitive = TDB.find "wft_def_UNION_primitive"
  fun op wft_def_UNION_extract1 _ = ()
  val op wft_def_UNION_extract1 = TDB.find "wft_def_UNION_extract1"
  fun op wft_def_UNION_extract0 _ = ()
  val op wft_def_UNION_extract0 = TDB.find "wft_def_UNION_extract0"
  fun op wfcod_def _ = () val op wfcod_def = TDB.find "wfcod_def"
  fun op trpl_def_UNION_primitive _ = ()
  val op trpl_def_UNION_primitive = TDB.find "trpl_def_UNION_primitive"
  fun op trpl_def_UNION_extract1 _ = ()
  val op trpl_def_UNION_extract1 = TDB.find "trpl_def_UNION_extract1"
  fun op trpl_def_UNION_extract0 _ = ()
  val op trpl_def_UNION_extract0 = TDB.find "trpl_def_UNION_extract0"
  fun op specsl_def _ = () val op specsl_def = TDB.find "specsl_def"
  fun op ok_abs_def _ = () val op ok_abs_def = TDB.find "ok_abs_def"
  fun op tshift_def_UNION_primitive _ = ()
  val op tshift_def_UNION_primitive = TDB.find "tshift_def_UNION_primitive"
  fun op tshift_def_UNION_extract1 _ = ()
  val op tshift_def_UNION_extract1 = TDB.find "tshift_def_UNION_extract1"
  fun op tshift_def_UNION_extract0 _ = ()
  val op tshift_def_UNION_extract0 = TDB.find "tshift_def_UNION_extract0"
  fun op shift_bmap_def _ = ()
  val op shift_bmap_def = TDB.find "shift_bmap_def"
  fun op mk_bmap_def _ = () val op mk_bmap_def = TDB.find "mk_bmap_def"
  fun op tsstt_def_UNION_primitive _ = ()
  val op tsstt_def_UNION_primitive = TDB.find "tsstt_def_UNION_primitive"
  fun op tsstt_def_UNION_extract1 _ = ()
  val op tsstt_def_UNION_extract1 = TDB.find "tsstt_def_UNION_extract1"
  fun op tsstt_def_UNION_extract0 _ = ()
  val op tsstt_def_UNION_extract0 = TDB.find "tsstt_def_UNION_extract0"
  fun op tsubst_def_UNION_primitive _ = ()
  val op tsubst_def_UNION_primitive = TDB.find "tsubst_def_UNION_primitive"
  fun op tsubst_def_UNION_extract1 _ = ()
  val op tsubst_def_UNION_extract1 = TDB.find "tsubst_def_UNION_extract1"
  fun op tsubst_def_UNION_extract0 _ = ()
  val op tsubst_def_UNION_extract0 = TDB.find "tsubst_def_UNION_extract0"
  fun op tlfv_def _ = () val op tlfv_def = TDB.find "tlfv_def"
  fun op tpsubtm_def _ = () val op tpsubtm_def = TDB.find "tpsubtm_def"
  fun op tabs_def_UNION_primitive _ = ()
  val op tabs_def_UNION_primitive = TDB.find "tabs_def_UNION_primitive"
  fun op tabs_def_UNION_extract1 _ = ()
  val op tabs_def_UNION_extract1 = TDB.find "tabs_def_UNION_extract1"
  fun op tabs_def_UNION_extract0 _ = ()
  val op tabs_def_UNION_extract0 = TDB.find "tabs_def_UNION_extract0"
  fun op slbounds_def _ = () val op slbounds_def = TDB.find "slbounds_def"
  fun op cvmap_def _ = () val op cvmap_def = TDB.find "cvmap_def"
  fun op evmap_def _ = () val op evmap_def = TDB.find "evmap_def"
  fun op tprpl_def_UNION_primitive _ = ()
  val op tprpl_def_UNION_primitive = TDB.find "tprpl_def_UNION_primitive"
  fun op tprpl_def_UNION_extract1 _ = ()
  val op tprpl_def_UNION_extract1 = TDB.find "tprpl_def_UNION_extract1"
  fun op tprpl_def_UNION_extract0 _ = ()
  val op tprpl_def_UNION_extract0 = TDB.find "tprpl_def_UNION_extract0"
  fun op FMAP_MAP_DEF _ = () val op FMAP_MAP_DEF = TDB.find "FMAP_MAP_DEF"
  fun op slprpl_def _ = () val op slprpl_def = TDB.find "slprpl_def"
  fun op BIGUNION_tbounds' _ = ()
  val op BIGUNION_tbounds' = TDB.find "BIGUNION_tbounds'"
  fun op sfv_tfv _ = () val op sfv_tfv = TDB.find "sfv_tfv"
  fun op sbounds_St _ = () val op sbounds_St = TDB.find "sbounds_St"
  fun op tbounds_Fn _ = () val op tbounds_Fn = TDB.find "tbounds_Fn"
  fun op tmatch_SOME_tinst _ = ()
  val op tmatch_SOME_tinst = TDB.find "tmatch_SOME_tinst"
  fun op UNION_is_cont _ = ()
  val op UNION_is_cont = TDB.find "UNION_is_cont"
  fun op complete_FDOM_is_cont _ = ()
  val op complete_FDOM_is_cont = TDB.find "complete_FDOM_is_cont"
  fun op tm_tree_size_less _ = ()
  val op tm_tree_size_less = TDB.find "tm_tree_size_less"
  fun op MEM_list_size_leq _ = ()
  val op MEM_list_size_leq = TDB.find "MEM_list_size_leq"
  fun op tinst_def _ = () val op tinst_def = TDB.find "tinst_def"
  fun op tinst_ind _ = () val op tinst_ind = TDB.find "tinst_ind"
  fun op tfv_thm _ = () val op tfv_thm = TDB.find "tfv_thm"
  fun op better_tm_induction _ = ()
  val op better_tm_induction = TDB.find "better_tm_induction"
  fun op tfv_def _ = () val op tfv_def = TDB.find "tfv_def"
  fun op tfv_ind _ = () val op tfv_ind = TDB.find "tfv_ind"
  fun op sort_case_eq _ = () val op sort_case_eq = TDB.find "sort_case_eq"
  fun op sort_case_cong _ = ()
  val op sort_case_cong = TDB.find "sort_case_cong"
  fun op sort_induction _ = ()
  val op sort_induction = TDB.find "sort_induction"
  fun op sort_Axiom _ = () val op sort_Axiom = TDB.find "sort_Axiom"
  fun op sort_nchotomy _ = ()
  val op sort_nchotomy = TDB.find "sort_nchotomy"
  fun op sort_11 _ = () val op sort_11 = TDB.find "sort_11"
  fun op term_case_eq _ = () val op term_case_eq = TDB.find "term_case_eq"
  fun op term_case_cong _ = ()
  val op term_case_cong = TDB.find "term_case_cong"
  fun op term_induction _ = ()
  val op term_induction = TDB.find "term_induction"
  fun op term_Axiom _ = () val op term_Axiom = TDB.find "term_Axiom"
  fun op term_nchotomy _ = ()
  val op term_nchotomy = TDB.find "term_nchotomy"
  fun op term_distinct _ = ()
  val op term_distinct = TDB.find "term_distinct"
  fun op term_11 _ = () val op term_11 = TDB.find "term_11"
  fun op datatype_term _ = ()
  val op datatype_term = TDB.find "datatype_term"
  fun op term_size_eq _ = () val op term_size_eq = TDB.find "term_size_eq"
  fun op match_complete _ = ()
  val op match_complete = TDB.find "match_complete"
  fun op wfvmap_cont_DRESTRICT _ = ()
  val op wfvmap_cont_DRESTRICT = TDB.find "wfvmap_cont_DRESTRICT"
  fun op tfv_is_cont _ = () val op tfv_is_cont = TDB.find "tfv_is_cont"
  fun op tlmatch_LENGTH _ = ()
  val op tlmatch_LENGTH = TDB.find "tlmatch_LENGTH"
  fun op vsort_tfv_closed _ = ()
  val op vsort_tfv_closed = TDB.find "vsort_tfv_closed"
  fun op DRESTRICT_UNION_SING _ = ()
  val op DRESTRICT_UNION_SING = TDB.find "DRESTRICT_UNION_SING"
  fun op vmap_fix_FEMPTY _ = ()
  val op vmap_fix_FEMPTY = TDB.find "vmap_fix_FEMPTY"
  fun op tinst_vmap_id _ = ()
  val op tinst_vmap_id = TDB.find "tinst_vmap_id"
  fun op fmap_fv_inst_eq _ = ()
  val op fmap_fv_inst_eq = TDB.find "fmap_fv_inst_eq"
  fun op tm_induction2 _ = ()
  val op tm_induction2 = TDB.find "tm_induction2"
  fun op tmatch_def _ = () val op tmatch_def = TDB.find "tmatch_def"
  fun op tmatch_ind _ = () val op tmatch_ind = TDB.find "tmatch_ind"
  fun op no_bound_not_bound _ = ()
  val op no_bound_not_bound = TDB.find "no_bound_not_bound"
  fun op is_bound_alt _ = () val op is_bound_alt = TDB.find "is_bound_alt"
  fun op tbounds_thm _ = () val op tbounds_thm = TDB.find "tbounds_thm"
  fun op tbounds_def _ = () val op tbounds_def = TDB.find "tbounds_def"
  fun op tbounds_ind _ = () val op tbounds_ind = TDB.find "tbounds_ind"
  fun op tm_tree_WF _ = () val op tm_tree_WF = TDB.find "tm_tree_WF"
  fun op match_SUBMAP _ = () val op match_SUBMAP = TDB.find "match_SUBMAP"
  fun op tmatch_FDOM_SUBMAP _ = ()
  val op tmatch_FDOM_SUBMAP = TDB.find "tmatch_FDOM_SUBMAP"
  fun op DRESTRICT_SUBMAP_SUBSET _ = ()
  val op DRESTRICT_SUBMAP_SUBSET = TDB.find "DRESTRICT_SUBMAP_SUBSET"
  fun op SUBMAP_DRESTRICT_IFF _ = ()
  val op SUBMAP_DRESTRICT_IFF = TDB.find "SUBMAP_DRESTRICT_IFF"
  fun op cstt_SUBMAP _ = () val op cstt_SUBMAP = TDB.find "cstt_SUBMAP"
  fun op match_SOME_cstt _ = ()
  val op match_SOME_cstt = TDB.find "match_SOME_cstt"
  fun op IS_SOME_match _ = ()
  val op IS_SOME_match = TDB.find "IS_SOME_match"
  fun op FEMPTY_complete _ = ()
  val op FEMPTY_complete = TDB.find "FEMPTY_complete"
  fun op FEMPTY_cstt _ = () val op FEMPTY_cstt = TDB.find "FEMPTY_cstt"
  fun op update_inst_lemma _ = ()
  val op update_inst_lemma = TDB.find "update_inst_lemma"
  fun op tmatch_FEMPTY_property _ = ()
  val op tmatch_FEMPTY_property = TDB.find "tmatch_FEMPTY_property"
  fun op no_bound_FUPDATE _ = ()
  val op no_bound_FUPDATE = TDB.find "no_bound_FUPDATE"
  fun op tmatch_no_bound _ = ()
  val op tmatch_no_bound = TDB.find "tmatch_no_bound"
  fun op FEMPTY_no_bound _ = ()
  val op FEMPTY_no_bound = TDB.find "FEMPTY_no_bound"
  fun op match_SOME_iff_inst _ = ()
  val op match_SOME_iff_inst = TDB.find "match_SOME_iff_inst"
  fun op FAPPLY_o_vmap _ = ()
  val op FAPPLY_o_vmap = TDB.find "FAPPLY_o_vmap"
  fun op FDOM_o_vmap _ = () val op FDOM_o_vmap = TDB.find "FDOM_o_vmap"
  fun op inst_o_vmap _ = () val op inst_o_vmap = TDB.find "inst_o_vmap"
  fun op match_SOME_iff_inst' _ = ()
  val op match_SOME_iff_inst' = TDB.find "match_SOME_iff_inst'"
  fun op cstt_sort_of_tinst' _ = ()
  val op cstt_sort_of_tinst' = TDB.find "cstt_sort_of_tinst'"
  fun op cstt_sort_of_tinst _ = ()
  val op cstt_sort_of_tinst = TDB.find "cstt_sort_of_tinst"
  fun op tsubtm_ind _ = () val op tsubtm_ind = TDB.find "tsubtm_ind"
  fun op tsubtm_def _ = () val op tsubtm_def = TDB.find "tsubtm_def"
  fun op tsubtm_REFL _ = () val op tsubtm_REFL = TDB.find "tsubtm_REFL"
  fun op fv_subtm _ = () val op fv_subtm = TDB.find "fv_subtm"
  fun op ssubtm_tsubtm _ = ()
  val op ssubtm_tsubtm = TDB.find "ssubtm_tsubtm"
  fun op no_bound_not_is_bound _ = ()
  val op no_bound_not_is_bound = TDB.find "no_bound_not_is_bound"
  fun op tinst_subtm _ = () val op tinst_subtm = TDB.find "tinst_subtm"
  fun op tfv_sinst _ = () val op tfv_sinst = TDB.find "tfv_sinst"
  fun op tmatch_TRANS_lemma _ = ()
  val op tmatch_TRANS_lemma = TDB.find "tmatch_TRANS_lemma"
  fun op sbounds_tbounds _ = ()
  val op sbounds_tbounds = TDB.find "sbounds_tbounds"
  fun op tbounds_EMPTY_tinst_no_bound _ = ()
  val op tbounds_EMPTY_tinst_no_bound = TDB.find
    "tbounds_EMPTY_tinst_no_bound"
  fun op o_vmap_no_bound _ = ()
  val op o_vmap_no_bound = TDB.find "o_vmap_no_bound"
  fun op tmatch_TRANS _ = () val op tmatch_TRANS = TDB.find "tmatch_TRANS"
  fun op DRESTRICT_no_bound _ = ()
  val op DRESTRICT_no_bound = TDB.find "DRESTRICT_no_bound"
  fun op tmatch_FEMPTY _ = ()
  val op tmatch_FEMPTY = TDB.find "tmatch_FEMPTY"
  fun op tlmatch_each_lemma _ = ()
  val op tlmatch_each_lemma = TDB.find "tlmatch_each_lemma"
  fun op FUNION_COMM1 _ = () val op FUNION_COMM1 = TDB.find "FUNION_COMM1"
  fun op tlmatch_each _ = () val op tlmatch_each = TDB.find "tlmatch_each"
  fun op tlmatch_FEMPTY_each _ = ()
  val op tlmatch_FEMPTY_each = TDB.find "tlmatch_FEMPTY_each"
  fun op IS_SOME_match_FEMPTY _ = ()
  val op IS_SOME_match_FEMPTY = TDB.find "IS_SOME_match_FEMPTY"
  fun op o_vmap_cstt _ = () val op o_vmap_cstt = TDB.find "o_vmap_cstt"
  fun op tlmatch_SOME_MAP _ = ()
  val op tlmatch_SOME_MAP = TDB.find "tlmatch_SOME_MAP"
  fun op tlmatch_tinst_imp_SOME _ = ()
  val op tlmatch_tinst_imp_SOME = TDB.find "tlmatch_tinst_imp_SOME"
  fun op tlmatch_tinst_imp_SOME' _ = ()
  val op tlmatch_tinst_imp_SOME' = TDB.find "tlmatch_tinst_imp_SOME'"
  fun op tlmatch_each_imp_tinst _ = ()
  val op tlmatch_each_imp_tinst = TDB.find "tlmatch_each_imp_tinst"
  fun op wft_ind _ = () val op wft_ind = TDB.find "wft_ind"
  fun op wft_def _ = () val op wft_def = TDB.find "wft_def"
  fun op wft_no_bound _ = () val op wft_no_bound = TDB.find "wft_no_bound"
  fun op wfcod_no_bound0 _ = ()
  val op wfcod_no_bound0 = TDB.find "wfcod_no_bound0"
  fun op wfcod_no_bound _ = ()
  val op wfcod_no_bound = TDB.find "wfcod_no_bound"
  fun op IS_SOME_tlmatch_inst _ = ()
  val op IS_SOME_tlmatch_inst = TDB.find "IS_SOME_tlmatch_inst"
  fun op wft_tinst _ = () val op wft_tinst = TDB.find "wft_tinst"
  fun op variant_ind _ = () val op variant_ind = TDB.find "variant_ind"
  fun op variant_def _ = () val op variant_def = TDB.find "variant_def"
  fun op variant_NOT_fIN _ = ()
  val op variant_NOT_fIN = TDB.find "variant_NOT_fIN"
  fun op variant_var_NOTIN _ = ()
  val op variant_var_NOTIN = TDB.find "variant_var_NOTIN"
  fun op trpl_ind _ = () val op trpl_ind = TDB.find "trpl_ind"
  fun op trpl_def _ = () val op trpl_def = TDB.find "trpl_def"
  fun op MAP_fix _ = () val op MAP_fix = TDB.find "MAP_fix"
  fun op trpl_id _ = () val op trpl_id = TDB.find "trpl_id"
  fun op wfabsap_ind _ = () val op wfabsap_ind = TDB.find "wfabsap_ind"
  fun op wfabsap_def _ = () val op wfabsap_def = TDB.find "wfabsap_def"
  fun op tshift_ind _ = () val op tshift_ind = TDB.find "tshift_ind"
  fun op tshift_def _ = () val op tshift_def = TDB.find "tshift_def"
  fun op tshift_id _ = () val op tshift_id = TDB.find "tshift_id"
  fun op Bound_tsubtm _ = () val op Bound_tsubtm = TDB.find "Bound_tsubtm"
  fun op trpl_eliminate0 _ = ()
  val op trpl_eliminate0 = TDB.find "trpl_eliminate0"
  fun op trpl_eliminate _ = ()
  val op trpl_eliminate = TDB.find "trpl_eliminate"
  fun op tsstt_ind _ = () val op tsstt_ind = TDB.find "tsstt_ind"
  fun op tsstt_def _ = () val op tsstt_def = TDB.find "tsstt_def"
  fun op tsubst_ind _ = () val op tsubst_ind = TDB.find "tsubst_ind"
  fun op tsubst_def _ = () val op tsubst_def = TDB.find "tsubst_def"
  fun op DRESTRICT_eq _ = () val op DRESTRICT_eq = TDB.find "DRESTRICT_eq"
  fun op fmap_fv_inst_eq_alt _ = ()
  val op fmap_fv_inst_eq_alt = TDB.find "fmap_fv_inst_eq_alt"
  fun op tfv_tinst_SUBSET_lemma _ = ()
  val op tfv_tinst_SUBSET_lemma = TDB.find "tfv_tinst_SUBSET_lemma"
  fun op tlmatch_EMPTY_TRANS_lemma _ = ()
  val op tlmatch_EMPTY_TRANS_lemma = TDB.find "tlmatch_EMPTY_TRANS_lemma"
  fun op tlmatch_TRANS_o_vmap _ = ()
  val op tlmatch_TRANS_o_vmap = TDB.find "tlmatch_TRANS_o_vmap"
  fun op FAPPLY_DOMSUB _ = ()
  val op FAPPLY_DOMSUB = TDB.find "FAPPLY_DOMSUB"
  fun op FUPDATE_cstt _ = () val op FUPDATE_cstt = TDB.find "FUPDATE_cstt"
  fun op tsubst_tsstt _ = () val op tsubst_tsstt = TDB.find "tsubst_tsstt"
  fun op tsstt_fix _ = () val op tsstt_fix = TDB.find "tsstt_fix"
  fun op subtm_size_less _ = ()
  val op subtm_size_less = TDB.find "subtm_size_less"
  fun op tsstt_tsubtm _ = () val op tsstt_tsubtm = TDB.find "tsstt_tsubtm"
  fun op tsstt_id _ = () val op tsstt_id = TDB.find "tsstt_id"
  fun op tpsubtm_size_LESS _ = ()
  val op tpsubtm_size_LESS = TDB.find "tpsubtm_size_LESS"
  fun op Var_tsubtm_tfv _ = ()
  val op Var_tsubtm_tfv = TDB.find "Var_tsubtm_tfv"
  fun op Var_tpsubtm _ = () val op Var_tpsubtm = TDB.find "Var_tpsubtm"
  fun op Fn_tpsubtm _ = () val op Fn_tpsubtm = TDB.find "Fn_tpsubtm"
  fun op Var_tpsubtm_neq _ = ()
  val op Var_tpsubtm_neq = TDB.find "Var_tpsubtm_neq"
  fun op Fn_tpsubtm_neq _ = ()
  val op Fn_tpsubtm_neq = TDB.find "Fn_tpsubtm_neq"
  fun op tsstt_itself _ = () val op tsstt_itself = TDB.find "tsstt_itself"
  fun op tsstt_tsstt _ = () val op tsstt_tsstt = TDB.find "tsstt_tsstt"
  fun op tsstt_tsstt1 _ = () val op tsstt_tsstt1 = TDB.find "tsstt_tsstt1"
  fun op tsstt_back _ = () val op tsstt_back = TDB.find "tsstt_back"
  fun op tlfv_is_cont _ = () val op tlfv_is_cont = TDB.find "tlfv_is_cont"
  fun op TO_FMAP_MEM _ = () val op TO_FMAP_MEM = TDB.find "TO_FMAP_MEM"
  fun op DRESTRICT_cstt _ = ()
  val op DRESTRICT_cstt = TDB.find "DRESTRICT_cstt"
  fun op tsubst_id _ = () val op tsubst_id = TDB.find "tsubst_id"
  fun op tfv_tsubst_SUBSET _ = ()
  val op tfv_tsubst_SUBSET = TDB.find "tfv_tsubst_SUBSET"
  fun op tabs_ind _ = () val op tabs_ind = TDB.find "tabs_ind"
  fun op tabs_def _ = () val op tabs_def = TDB.find "tabs_def"
  fun op tabs_tsubst _ = () val op tabs_tsubst = TDB.find "tabs_tsubst"
  fun op tfv_tabs_SUBSET _ = ()
  val op tfv_tabs_SUBSET = TDB.find "tfv_tabs_SUBSET"
  fun op tabs_id _ = () val op tabs_id = TDB.find "tabs_id"
  fun op tabs_tinst _ = () val op tabs_tinst = TDB.find "tabs_tinst"
  fun op tsubst_tinst _ = () val op tsubst_tinst = TDB.find "tsubst_tinst"
  fun op sabs_sinst _ = () val op sabs_sinst = TDB.find "sabs_sinst"
  fun op ssubst_sinst _ = () val op ssubst_sinst = TDB.find "ssubst_sinst"
  fun op tsubst_id' _ = () val op tsubst_id' = TDB.find "tsubst_id'"
  fun op tfv_tsubst _ = () val op tfv_tsubst = TDB.find "tfv_tsubst"
  fun op tfv_tabs _ = () val op tfv_tabs = TDB.find "tfv_tabs"
  fun op DRESTRICT_wfcod _ = ()
  val op DRESTRICT_wfcod = TDB.find "DRESTRICT_wfcod"
  fun op FUPDATE_wfcod _ = ()
  val op FUPDATE_wfcod = TDB.find "FUPDATE_wfcod"
  fun op tfv_FINITE _ = () val op tfv_FINITE = TDB.find "tfv_FINITE"
  fun op FDOM_TO_FMAP _ = () val op FDOM_TO_FMAP = TDB.find "FDOM_TO_FMAP"
  fun op tsubst_eq_tinst _ = ()
  val op tsubst_eq_tinst = TDB.find "tsubst_eq_tinst"
  fun op wft_tbounds _ = () val op wft_tbounds = TDB.find "wft_tbounds"
  fun op Bound_NOT_wft _ = ()
  val op Bound_NOT_wft = TDB.find "Bound_NOT_wft"
  fun op tfv_tsubtm_closed _ = ()
  val op tfv_tsubtm_closed = TDB.find "tfv_tsubtm_closed"
  fun op wfabsap_sfv_sbounds _ = ()
  val op wfabsap_sfv_sbounds = TDB.find "wfabsap_sfv_sbounds"
  fun op LENGTH_specsl _ = ()
  val op LENGTH_specsl = TDB.find "LENGTH_specsl"
  fun op specsl_sbounds _ = ()
  val op specsl_sbounds = TDB.find "specsl_sbounds"
  fun op specsl_sbounds_SUBSET _ = ()
  val op specsl_sbounds_SUBSET = TDB.find "specsl_sbounds_SUBSET"
  fun op wfabsap_ok_abs _ = ()
  val op wfabsap_ok_abs = TDB.find "wfabsap_ok_abs"
  fun op wfabsap_wft _ = () val op wfabsap_wft = TDB.find "wfabsap_wft"
  fun op sinst_srpl _ = () val op sinst_srpl = TDB.find "sinst_srpl"
  fun op ok_abs_HD _ = () val op ok_abs_HD = TDB.find "ok_abs_HD"
  fun op MAP_sinst_specsl _ = ()
  val op MAP_sinst_specsl = TDB.find "MAP_sinst_specsl"
  fun op specsl_EL _ = () val op specsl_EL = TDB.find "specsl_EL"
  fun op tfv_trpl _ = () val op tfv_trpl = TDB.find "tfv_trpl"
  fun op tfv_trpl_SUBSET _ = ()
  val op tfv_trpl_SUBSET = TDB.find "tfv_trpl_SUBSET"
  fun op wfabsap_sfv_SUBSET _ = ()
  val op wfabsap_sfv_SUBSET = TDB.find "wfabsap_sfv_SUBSET"
  fun op wfabsap_sinst_tinst _ = ()
  val op wfabsap_sinst_tinst = TDB.find "wfabsap_sinst_tinst"
  fun op tsubst_eq_tinst1 _ = ()
  val op tsubst_eq_tinst1 = TDB.find "tsubst_eq_tinst1"
  fun op abssl_ind _ = () val op abssl_ind = TDB.find "abssl_ind"
  fun op abssl_def _ = () val op abssl_def = TDB.find "abssl_def"
  fun op trpl_tabs _ = () val op trpl_tabs = TDB.find "trpl_tabs"
  fun op slabs_ind _ = () val op slabs_ind = TDB.find "slabs_ind"
  fun op slabs_def _ = () val op slabs_def = TDB.find "slabs_def"
  fun op slabs_abssl _ = () val op slabs_abssl = TDB.find "slabs_abssl"
  fun op specsl_abssl _ = () val op specsl_abssl = TDB.find "specsl_abssl"
  fun op slbounds_sbounds _ = ()
  val op slbounds_sbounds = TDB.find "slbounds_sbounds"
  fun op tinst_tsubst _ = () val op tinst_tsubst = TDB.find "tinst_tsubst"
  fun op tinst_tabs _ = () val op tinst_tabs = TDB.find "tinst_tabs"
  fun op MAP_sinst_abssl _ = ()
  val op MAP_sinst_abssl = TDB.find "MAP_sinst_abssl"
  fun op cstt_cvmap _ = () val op cstt_cvmap = TDB.find "cstt_cvmap"
  fun op FDOM_cvmap _ = () val op FDOM_cvmap = TDB.find "FDOM_cvmap"
  fun op FDOM_evmap _ = () val op FDOM_evmap = TDB.find "FDOM_evmap"
  fun op FAPPLY_cvmap _ = () val op FAPPLY_cvmap = TDB.find "FAPPLY_cvmap"
  fun op cstt_FUPDATE _ = () val op cstt_FUPDATE = TDB.find "cstt_FUPDATE"
  fun op slbounds_specsl_DELETE _ = ()
  val op slbounds_specsl_DELETE = TDB.find "slbounds_specsl_DELETE"
  fun op wfabsap_slbounds _ = ()
  val op wfabsap_slbounds = TDB.find "wfabsap_slbounds"
  fun op tsubst_tbounds_in _ = ()
  val op tsubst_tbounds_in = TDB.find "tsubst_tbounds_in"
  fun op tbounds_tsubst_SUBSET _ = ()
  val op tbounds_tsubst_SUBSET = TDB.find "tbounds_tsubst_SUBSET"
  fun op tbounds_tabs_SUBSET _ = ()
  val op tbounds_tabs_SUBSET = TDB.find "tbounds_tabs_SUBSET"
  fun op tbounds_tsubst _ = ()
  val op tbounds_tsubst = TDB.find "tbounds_tsubst"
  fun op IN_slbounds _ = () val op IN_slbounds = TDB.find "IN_slbounds"
  fun op slabs_EL _ = () val op slabs_EL = TDB.find "slabs_EL"
  fun op LENGTH_slabs _ = () val op LENGTH_slabs = TDB.find "LENGTH_slabs"
  fun op tabs_tbounds_in _ = ()
  val op tabs_tbounds_in = TDB.find "tabs_tbounds_in"
  fun op abssl_EL _ = () val op abssl_EL = TDB.find "abssl_EL"
  fun op tbounds_tabs _ = () val op tbounds_tabs = TDB.find "tbounds_tabs"
  fun op LENGTH_abssl _ = () val op LENGTH_abssl = TDB.find "LENGTH_abssl"
  fun op slbounds_abssl _ = ()
  val op slbounds_abssl = TDB.find "slbounds_abssl"
  fun op slbounds_slabs _ = ()
  val op slbounds_slabs = TDB.find "slbounds_slabs"
  fun op BIGUNION_tbounds _ = ()
  val op BIGUNION_tbounds = TDB.find "BIGUNION_tbounds"
  fun op NOTIN_slbounds_abssl _ = ()
  val op NOTIN_slbounds_abssl = TDB.find "NOTIN_slbounds_abssl"
  fun op NOTIN_slbounds_slabs _ = ()
  val op NOTIN_slbounds_slabs = TDB.find "NOTIN_slbounds_slabs"
  fun op wft_tsubtm _ = () val op wft_tsubtm = TDB.find "wft_tsubtm"
  fun op wft_wfs _ = () val op wft_wfs = TDB.find "wft_wfs"
  fun op wfabsap_wfs _ = () val op wfabsap_wfs = TDB.find "wfabsap_wfs"
  fun op tinst_eq_cvmap _ = ()
  val op tinst_eq_cvmap = TDB.find "tinst_eq_cvmap"
  fun op tprpl_ind _ = () val op tprpl_ind = TDB.find "tprpl_ind"
  fun op tprpl_def _ = () val op tprpl_def = TDB.find "tprpl_def"
  fun op FAPPLY_mk_bmap _ = ()
  val op FAPPLY_mk_bmap = TDB.find "FAPPLY_mk_bmap"
  fun op FDOM_mk_bmap _ = () val op FDOM_mk_bmap = TDB.find "FDOM_mk_bmap"
  fun op FAPPLY_FMAP_MAP _ = ()
  val op FAPPLY_FMAP_MAP = TDB.find "FAPPLY_FMAP_MAP"
  fun op FDOM_FMAP_MAP _ = ()
  val op FDOM_FMAP_MAP = TDB.find "FDOM_FMAP_MAP"
  fun op tprpl_FMAP_MAP_tabs _ = ()
  val op tprpl_FMAP_MAP_tabs = TDB.find "tprpl_FMAP_MAP_tabs"
  fun op tprpl_FEMPTY _ = () val op tprpl_FEMPTY = TDB.find "tprpl_FEMPTY"
  fun op shift_bmap_FEMPTY _ = ()
  val op shift_bmap_FEMPTY = TDB.find "shift_bmap_FEMPTY"
  fun op slprpl_FEMPTY _ = ()
  val op slprpl_FEMPTY = TDB.find "slprpl_FEMPTY"
  fun op tshift_0 _ = () val op tshift_0 = TDB.find "tshift_0"
  fun op shift_bmap_0 _ = () val op shift_bmap_0 = TDB.find "shift_bmap_0"
  fun op FDOM_FINITE_lemma _ = ()
  val op FDOM_FINITE_lemma = TDB.find "FDOM_FINITE_lemma"
  fun op tshift_SUM _ = () val op tshift_SUM = TDB.find "tshift_SUM"
  fun op shift_bmap_SUM _ = ()
  val op shift_bmap_SUM = TDB.find "shift_bmap_SUM"
  fun op slprpl_EL _ = () val op slprpl_EL = TDB.find "slprpl_EL"
  fun op tshift_tabs _ = () val op tshift_tabs = TDB.find "tshift_tabs"
  fun op shift_bmap_FMAP_MAP_tabs _ = ()
  val op shift_bmap_FMAP_MAP_tabs = TDB.find "shift_bmap_FMAP_MAP_tabs"
  fun op LENGTH_slprpl _ = ()
  val op LENGTH_slprpl = TDB.find "LENGTH_slprpl"
  fun op NOT_ok_abs _ = () val op NOT_ok_abs = TDB.find "NOT_ok_abs"
  fun op NOT_ok_abssl _ = () val op NOT_ok_abssl = TDB.find "NOT_ok_abssl"
  fun op slabs_id _ = () val op slabs_id = TDB.find "slabs_id"
  fun op abssl_id _ = () val op abssl_id = TDB.find "abssl_id"
  fun op ok_abs_abssl _ = () val op ok_abs_abssl = TDB.find "ok_abs_abssl"
  fun op tfv_tprpl _ = () val op tfv_tprpl = TDB.find "tfv_tprpl"
  fun op abssl_ok_abs _ = () val op abssl_ok_abs = TDB.find "abssl_ok_abs"
  fun op mk_bmap_MAP _ = () val op mk_bmap_MAP = TDB.find "mk_bmap_MAP"
  fun op FDOM_shift_bmap _ = ()
  val op FDOM_shift_bmap = TDB.find "FDOM_shift_bmap"
  fun op FAPPLY_shift_bmap _ = ()
  val op FAPPLY_shift_bmap = TDB.find "FAPPLY_shift_bmap"
  fun op tfv_tshift _ = () val op tfv_tshift = TDB.find "tfv_tshift"
  fun op tprpl_id _ = () val op tprpl_id = TDB.find "tprpl_id"
  fun op EL_REVERSE1 _ = () val op EL_REVERSE1 = TDB.find "EL_REVERSE1"
  fun op EL_REVERSE2 _ = () val op EL_REVERSE2 = TDB.find "EL_REVERSE2"
  fun op tprpl_mk_bmap_CONS _ = ()
  val op tprpl_mk_bmap_CONS = TDB.find "tprpl_mk_bmap_CONS"
  fun op tabs_trpl _ = () val op tabs_trpl = TDB.find "tabs_trpl"
  fun op abssl_specsl _ = () val op abssl_specsl = TDB.find "abssl_specsl"
  fun op wfabsap_LENGTH _ = ()
  val op wfabsap_LENGTH = TDB.find "wfabsap_LENGTH"
  fun op ill_formed_tabs_still_in _ = ()
  val op ill_formed_tabs_still_in = TDB.find "ill_formed_tabs_still_in"
  
  
val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "tmsytx"

val tmsytx_grammars = valOf (Parse.grammarDB {thyname = "tmsytx"})
end
