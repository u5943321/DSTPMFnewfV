structure wfgenl1Theory :> wfgenl1Theory =
struct
  
  val _ = if !Globals.print_thy_loads
    then TextIO.print "Loading wfgenl1Theory ... "
    else ()
  
  open Type Term Thm
  local open fVinst1Theory in end;
  
  structure TDB = struct
    val thydata = 
      TheoryReader.load_thydata "wfgenl1"
        (holpathdb.subst_pathvars "/Users/yimingxu/Documents/GitHub/DSTPMFnewfV/formal/wfgenl1Theory.dat")
    fun find s = HOLdict.find (thydata,s)
  end
  
  fun op vl2sl0_def _ = () val op vl2sl0_def = TDB.find "vl2sl0_def"
  fun op vl2sl_def _ = () val op vl2sl_def = TDB.find "vl2sl_def"
  fun op tpv2b_def_UNION_primitive _ = ()
  val op tpv2b_def_UNION_primitive = TDB.find "tpv2b_def_UNION_primitive"
  fun op tpv2b_def_UNION_extract1 _ = ()
  val op tpv2b_def_UNION_extract1 = TDB.find "tpv2b_def_UNION_extract1"
  fun op tpv2b_def_UNION_extract0 _ = ()
  val op tpv2b_def_UNION_extract0 = TDB.find "tpv2b_def_UNION_extract0"
  fun op vpv2b_def _ = () val op vpv2b_def = TDB.find "vpv2b_def"
  fun op mk_v2b_def _ = () val op mk_v2b_def = TDB.find "mk_v2b_def"
  fun op fpv2b_def _ = () val op fpv2b_def = TDB.find "fpv2b_def"
  fun op plainfV_def _ = () val op plainfV_def = TDB.find "plainfV_def"
  fun op wfdpvl_def _ = () val op wfdpvl_def = TDB.find "wfdpvl_def"
  fun op wfvl_def _ = () val op wfvl_def = TDB.find "wfvl_def"
  fun op okvnames_def _ = () val op okvnames_def = TDB.find "okvnames_def"
  fun op wffstl_def _ = () val op wffstl_def = TDB.find "wffstl_def"
  fun op fresh_to_def _ = () val op fresh_to_def = TDB.find "fresh_to_def"
  fun op tnames_def_UNION_primitive _ = ()
  val op tnames_def_UNION_primitive = TDB.find "tnames_def_UNION_primitive"
  fun op tnames_def_UNION_extract1 _ = ()
  val op tnames_def_UNION_extract1 = TDB.find "tnames_def_UNION_extract1"
  fun op tnames_def_UNION_extract0 _ = ()
  val op tnames_def_UNION_extract0 = TDB.find "tnames_def_UNION_extract0"
  fun op slnames_def _ = () val op slnames_def = TDB.find "slnames_def"
  fun op tlnames_def _ = () val op tlnames_def = TDB.find "tlnames_def"
  fun op wffVsl_def _ = () val op wffVsl_def = TDB.find "wffVsl_def"
  fun op mk_FALLL_ind _ = () val op mk_FALLL_ind = TDB.find "mk_FALLL_ind"
  fun op mk_FALLL_def _ = () val op mk_FALLL_def = TDB.find "mk_FALLL_def"
  fun op mk_FALL_FALLL0 _ = ()
  val op mk_FALL_FALLL0 = TDB.find "mk_FALL_FALLL0"
  fun op fVslfv_fabs _ = () val op fVslfv_fabs = TDB.find "fVslfv_fabs"
  fun op fVslfv_mk_FALL _ = ()
  val op fVslfv_mk_FALL = TDB.find "fVslfv_mk_FALL"
  fun op fVslfv_mk_FALLL _ = ()
  val op fVslfv_mk_FALLL = TDB.find "fVslfv_mk_FALLL"
  fun op DIFF_of_UNION _ = ()
  val op DIFF_of_UNION = TDB.find "DIFF_of_UNION"
  fun op absvl_ind _ = () val op absvl_ind = TDB.find "absvl_ind"
  fun op absvl_def _ = () val op absvl_def = TDB.find "absvl_def"
  fun op fVars_mk_FALL _ = ()
  val op fVars_mk_FALL = TDB.find "fVars_mk_FALL"
  fun op fVars_mk_FALLL _ = ()
  val op fVars_mk_FALLL = TDB.find "fVars_mk_FALLL"
  fun op tpv2b_ind _ = () val op tpv2b_ind = TDB.find "tpv2b_ind"
  fun op tpv2b_def _ = () val op tpv2b_def = TDB.find "tpv2b_def"
  fun op FAPPLY_mk_v2b _ = ()
  val op FAPPLY_mk_v2b = TDB.find "FAPPLY_mk_v2b"
  fun op vl2sl_EMPTY _ = () val op vl2sl_EMPTY = TDB.find "vl2sl_EMPTY"
  fun op TAKE_LAST _ = () val op TAKE_LAST = TDB.find "TAKE_LAST"
  fun op mk_FALL_FALLL _ = ()
  val op mk_FALL_FALLL = TDB.find "mk_FALL_FALLL"
  fun op MAP_SND_absvl0 _ = ()
  val op MAP_SND_absvl0 = TDB.find "MAP_SND_absvl0"
  fun op MAP_SND_absvl _ = ()
  val op MAP_SND_absvl = TDB.find "MAP_SND_absvl"
  fun op vl2sl_CONS _ = () val op vl2sl_CONS = TDB.find "vl2sl_CONS"
  fun op LENGTH_absvl _ = () val op LENGTH_absvl = TDB.find "LENGTH_absvl"
  fun op LENGTH_vl2sl0 _ = ()
  val op LENGTH_vl2sl0 = TDB.find "LENGTH_vl2sl0"
  fun op LENGTH_vl2sl _ = () val op LENGTH_vl2sl = TDB.find "LENGTH_vl2sl"
  fun op tabs_tpv2b _ = () val op tabs_tpv2b = TDB.find "tabs_tpv2b"
  fun op vpv2b_tpv2b _ = () val op vpv2b_tpv2b = TDB.find "vpv2b_tpv2b"
  fun op FDOM_mk_v2b _ = () val op FDOM_mk_v2b = TDB.find "FDOM_mk_v2b"
  fun op FAPPLY_mk_v2b_APPEND _ = ()
  val op FAPPLY_mk_v2b_APPEND = TDB.find "FAPPLY_mk_v2b_APPEND"
  fun op mk_v2b_FUPDATE _ = ()
  val op mk_v2b_FUPDATE = TDB.find "mk_v2b_FUPDATE"
  fun op mk_v2b_EMPTY_FUPDATE _ = ()
  val op mk_v2b_EMPTY_FUPDATE = TDB.find "mk_v2b_EMPTY_FUPDATE"
  fun op ALL_DISTINCT_TAKE _ = ()
  val op ALL_DISTINCT_TAKE = TDB.find "ALL_DISTINCT_TAKE"
  fun op mk_FALLL_fVar _ = ()
  val op mk_FALLL_fVar = TDB.find "mk_FALLL_fVar"
  fun op mk_FALLL_fVar1 _ = ()
  val op mk_FALLL_fVar1 = TDB.find "mk_FALLL_fVar1"
  fun op vpv2b_mk_v2b_EL _ = ()
  val op vpv2b_mk_v2b_EL = TDB.find "vpv2b_mk_v2b_EL"
  fun op fVar_MAP_vpv2b _ = ()
  val op fVar_MAP_vpv2b = TDB.find "fVar_MAP_vpv2b"
  fun op mk_FALLL_fVar_FALLL _ = ()
  val op mk_FALLL_fVar_FALLL = TDB.find "mk_FALLL_fVar_FALLL"
  fun op fVslfv_mk_FALLL1 _ = ()
  val op fVslfv_mk_FALLL1 = TDB.find "fVslfv_mk_FALLL1"
  fun op fabs_False _ = () val op fabs_False = TDB.find "fabs_False"
  fun op mk_FALLL_False _ = ()
  val op mk_FALLL_False = TDB.find "mk_FALLL_False"
  fun op ffv_False _ = () val op ffv_False = TDB.find "ffv_False"
  fun op tfv_tpv2b_SUBSET _ = ()
  val op tfv_tpv2b_SUBSET = TDB.find "tfv_tpv2b_SUBSET"
  fun op tlfv_MAP_Bound_EMPTY _ = ()
  val op tlfv_MAP_Bound_EMPTY = TDB.find "tlfv_MAP_Bound_EMPTY"
  fun op slfv_alt _ = () val op slfv_alt = TDB.find "slfv_alt"
  fun op tfv_tabs_SUBSET1 _ = ()
  val op tfv_tabs_SUBSET1 = TDB.find "tfv_tabs_SUBSET1"
  fun op slfv_CONS _ = () val op slfv_CONS = TDB.find "slfv_CONS"
  fun op slfv_abssl _ = () val op slfv_abssl = TDB.find "slfv_abssl"
  fun op wfdpvl_ffv_mk_FALLL _ = ()
  val op wfdpvl_ffv_mk_FALLL = TDB.find "wfdpvl_ffv_mk_FALLL"
  fun op okvnames_CONS _ = ()
  val op okvnames_CONS = TDB.find "okvnames_CONS"
  fun op wfdpvl_expand _ = ()
  val op wfdpvl_expand = TDB.find "wfdpvl_expand"
  fun op tlfv_CONS _ = () val op tlfv_CONS = TDB.find "tlfv_CONS"
  fun op slfv_abssl_SUBSET _ = ()
  val op slfv_abssl_SUBSET = TDB.find "slfv_abssl_SUBSET"
  fun op slfv_vl2sl_SUBSET _ = ()
  val op slfv_vl2sl_SUBSET = TDB.find "slfv_vl2sl_SUBSET"
  fun op NOTIN_slfv_abssl _ = ()
  val op NOTIN_slfv_abssl = TDB.find "NOTIN_slfv_abssl"
  fun op wfdpvl_NOTIN_slfv _ = ()
  val op wfdpvl_NOTIN_slfv = TDB.find "wfdpvl_NOTIN_slfv"
  fun op fVslfv_fVar _ = () val op fVslfv_fVar = TDB.find "fVslfv_fVar"
  fun op vpv2b_NOTIN _ = () val op vpv2b_NOTIN = TDB.find "vpv2b_NOTIN"
  fun op ffv_FALLL_fVar_CONS _ = ()
  val op ffv_FALLL_fVar_CONS = TDB.find "ffv_FALLL_fVar_CONS"
  fun op ffv_fVar_vl2sl _ = ()
  val op ffv_fVar_vl2sl = TDB.find "ffv_fVar_vl2sl"
  fun op DIFF_of_UNION1 _ = ()
  val op DIFF_of_UNION1 = TDB.find "DIFF_of_UNION1"
  fun op DIFF_SUBSET _ = () val op DIFF_SUBSET = TDB.find "DIFF_SUBSET"
  fun op fVar_CONS_ffv_DIFF _ = ()
  val op fVar_CONS_ffv_DIFF = TDB.find "fVar_CONS_ffv_DIFF"
  fun op fVar_CONS_ffv_DIFF1 _ = ()
  val op fVar_CONS_ffv_DIFF1 = TDB.find "fVar_CONS_ffv_DIFF1"
  fun op wfdpvl_False_fVar _ = ()
  val op wfdpvl_False_fVar = TDB.find "wfdpvl_False_fVar"
  fun op sl2vl_ind _ = () val op sl2vl_ind = TDB.find "sl2vl_ind"
  fun op sl2vl_def _ = () val op sl2vl_def = TDB.find "sl2vl_def"
  fun op slfv_EMPTY _ = () val op slfv_EMPTY = TDB.find "slfv_EMPTY"
  fun op tnames_ind _ = () val op tnames_ind = TDB.find "tnames_ind"
  fun op tnames_def _ = () val op tnames_def = TDB.find "tnames_def"
  fun op slnames_alt _ = () val op slnames_alt = TDB.find "slnames_alt"
  fun op tlnames_alt _ = () val op tlnames_alt = TDB.find "tlnames_alt"
  fun op tnames_thm _ = () val op tnames_thm = TDB.find "tnames_thm"
  fun op tnames_trpl_SUBSET _ = ()
  val op tnames_trpl_SUBSET = TDB.find "tnames_trpl_SUBSET"
  fun op vl2sl_sl2vl_names_lemma _ = ()
  val op vl2sl_sl2vl_names_lemma = TDB.find "vl2sl_sl2vl_names_lemma"
  fun op slnames_CONS _ = () val op slnames_CONS = TDB.find "slnames_CONS"
  fun op tfv_tnames _ = () val op tfv_tnames = TDB.find "tfv_tnames"
  fun op vl2sl_sl2vl _ = () val op vl2sl_sl2vl = TDB.find "vl2sl_sl2vl"
  fun op fVars_False _ = () val op fVars_False = TDB.find "fVars_False"
  fun op fVslfv_False _ = () val op fVslfv_False = TDB.find "fVslfv_False"
  fun op wfdpvl_False _ = () val op wfdpvl_False = TDB.find "wfdpvl_False"
  fun op MAP_FST_sl2vl _ = ()
  val op MAP_FST_sl2vl = TDB.find "MAP_FST_sl2vl"
  fun op ALL_DISTINCT_sl2vl _ = ()
  val op ALL_DISTINCT_sl2vl = TDB.find "ALL_DISTINCT_sl2vl"
  fun op ALL_DISTINCT_EMPTY_INTER_lemma _ = ()
  val op ALL_DISTINCT_EMPTY_INTER_lemma = TDB.find
    "ALL_DISTINCT_EMPTY_INTER_lemma"
  fun op okvnames_sl2vl _ = ()
  val op okvnames_sl2vl = TDB.find "okvnames_sl2vl"
  fun op tfv_trpl_SUBSET2 _ = ()
  val op tfv_trpl_SUBSET2 = TDB.find "tfv_trpl_SUBSET2"
  fun op slfv_specsl _ = () val op slfv_specsl = TDB.find "slfv_specsl"
  fun op sfv_slfv_slnames _ = ()
  val op sfv_slfv_slnames = TDB.find "sfv_slfv_slnames"
  fun op wfdpvl_sl2vl _ = () val op wfdpvl_sl2vl = TDB.find "wfdpvl_sl2vl"
  fun op sl2vl_sinst _ = () val op sl2vl_sinst = TDB.find "sl2vl_sinst"
  fun op vl2sl_no_vbound _ = ()
  val op vl2sl_no_vbound = TDB.find "vl2sl_no_vbound"
  fun op tbounds_tabs_SUBSET1 _ = ()
  val op tbounds_tabs_SUBSET1 = TDB.find "tbounds_tabs_SUBSET1"
  fun op ok_abs_vl2sl _ = () val op ok_abs_vl2sl = TDB.find "ok_abs_vl2sl"
  fun op wft_tinst1 _ = () val op wft_tinst1 = TDB.find "wft_tinst1"
  fun op wfs_sinst1 _ = () val op wfs_sinst1 = TDB.find "wfs_sinst1"
  fun op TO_FMAP_EMPTY _ = ()
  val op TO_FMAP_EMPTY = TDB.find "TO_FMAP_EMPTY"
  fun op cstt_FEMPTY _ = () val op cstt_FEMPTY = TDB.find "cstt_FEMPTY"
  fun op trename_reflect _ = ()
  val op trename_reflect = TDB.find "trename_reflect"
  fun op trename_tabs _ = () val op trename_tabs = TDB.find "trename_tabs"
  fun op MAP_ssubst_abssl _ = ()
  val op MAP_ssubst_abssl = TDB.find "MAP_ssubst_abssl"
  fun op MAP_srename_abssl _ = ()
  val op MAP_srename_abssl = TDB.find "MAP_srename_abssl"
  fun op tlnames_CONS _ = () val op tlnames_CONS = TDB.find "tlnames_CONS"
  fun op NOT_IN_abssl _ = () val op NOT_IN_abssl = TDB.find "NOT_IN_abssl"
  fun op wfdpvl_NOTIN_sfv _ = ()
  val op wfdpvl_NOTIN_sfv = TDB.find "wfdpvl_NOTIN_sfv"
  fun op wfdpvl_MEM_NOT_slfv _ = ()
  val op wfdpvl_MEM_NOT_slfv = TDB.find "wfdpvl_MEM_NOT_slfv"
  fun op wfvar_vl2sl_wfvar _ = ()
  val op wfvar_vl2sl_wfvar = TDB.find "wfvar_vl2sl_wfvar"
  fun op tnames_tabs _ = () val op tnames_tabs = TDB.find "tnames_tabs"
  fun op slnames_abssl_SUBSET _ = ()
  val op slnames_abssl_SUBSET = TDB.find "slnames_abssl_SUBSET"
  fun op slnames_vl2sl_SUBSET _ = ()
  val op slnames_vl2sl_SUBSET = TDB.find "slnames_vl2sl_SUBSET"
  fun op srename_vl2sl _ = ()
  val op srename_vl2sl = TDB.find "srename_vl2sl"
  fun op tsubst_trename _ = ()
  val op tsubst_trename = TDB.find "tsubst_trename"
  fun op tsubst_trename1 _ = ()
  val op tsubst_trename1 = TDB.find "tsubst_trename1"
  fun op slfv_is_cont _ = () val op slfv_is_cont = TDB.find "slfv_is_cont"
  fun op sfv_tfv_lemma _ = ()
  val op sfv_tfv_lemma = TDB.find "sfv_tfv_lemma"
  fun op term_size_term_var_sort_tl_less _ = ()
  val op term_size_term_var_sort_tl_less = TDB.find
    "term_size_term_var_sort_tl_less"
  fun op tfv_trename1 _ = () val op tfv_trename1 = TDB.find "tfv_trename1"
  fun op Uof_eq_lemma _ = () val op Uof_eq_lemma = TDB.find "Uof_eq_lemma"
  fun op Uof_IMAGE _ = () val op Uof_IMAGE = TDB.find "Uof_IMAGE"
  fun op sfv_srename1 _ = () val op sfv_srename1 = TDB.find "sfv_srename1"
  fun op vname_tfv_closed _ = ()
  val op vname_tfv_closed = TDB.find "vname_tfv_closed"
  fun op IN_trename_names _ = ()
  val op IN_trename_names = TDB.find "IN_trename_names"
  fun op NOTIN_trename_names _ = ()
  val op NOTIN_trename_names = TDB.find "NOTIN_trename_names"
  fun op srename_same_IN_iff _ = ()
  val op srename_same_IN_iff = TDB.find "srename_same_IN_iff"
  fun op wfdpvl_rename _ = ()
  val op wfdpvl_rename = TDB.find "wfdpvl_rename"
  fun op okvnames_MAP_srename _ = ()
  val op okvnames_MAP_srename = TDB.find "okvnames_MAP_srename"
  fun op tnames_trename_SUBSET _ = ()
  val op tnames_trename_SUBSET = TDB.find "tnames_trename_SUBSET"
  fun op wfvl_sl2vl_vl2sl _ = ()
  val op wfvl_sl2vl_vl2sl = TDB.find "wfvl_sl2vl_vl2sl"
  fun op variant_NOT_SUBSET _ = ()
  val op variant_NOT_SUBSET = TDB.find "variant_NOT_SUBSET"
  fun op nl_EX _ = () val op nl_EX = TDB.find "nl_EX"
  fun op tnames_FINITE _ = ()
  val op tnames_FINITE = TDB.find "tnames_FINITE"
  fun op tlnames_FINITE _ = ()
  val op tlnames_FINITE = TDB.find "tlnames_FINITE"
  fun op slnames_FINITE _ = ()
  val op slnames_FINITE = TDB.find "slnames_FINITE"
  fun op wffVsl_sinst _ = () val op wffVsl_sinst = TDB.find "wffVsl_sinst"
  fun op tinst_wffstl _ = () val op tinst_wffstl = TDB.find "tinst_wffstl"
  fun op IN_Uof _ = () val op IN_Uof = TDB.find "IN_Uof"
  fun op vl2sl_fix _ = () val op vl2sl_fix = TDB.find "vl2sl_fix"
  fun op wfvl_alt _ = () val op wfvl_alt = TDB.find "wfvl_alt"
  fun op wfs_wffVsl_wfvl_lemma _ = ()
  val op wfs_wffVsl_wfvl_lemma = TDB.find "wfs_wffVsl_wfvl_lemma"
  fun op specsl_wfs_fix _ = ()
  val op specsl_wfs_fix = TDB.find "specsl_wfs_fix"
  fun op sl2vl_no_bound _ = ()
  val op sl2vl_no_bound = TDB.find "sl2vl_no_bound"
  fun op wfs_wffVsl _ = () val op wfs_wffVsl = TDB.find "wfs_wffVsl"
  fun op wfabsap_of_wfsl _ = ()
  val op wfabsap_of_wfsl = TDB.find "wfabsap_of_wfsl"
  
  
val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "wfgenl1"

val wfgenl1_grammars = valOf (Parse.grammarDB {thyname = "wfgenl1"})
end
