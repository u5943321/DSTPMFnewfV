structure fsytxTheory :> fsytxTheory =
struct
  
  val _ = if !Globals.print_thy_loads
    then TextIO.print "Loading fsytxTheory ... "
    else ()
  
  open Type Term Thm
  local open tmsytxTheory in end;
  
  structure TDB = struct
    val thydata = 
      TheoryReader.load_thydata "fsytx"
        (holpathdb.subst_pathvars "/Users/yimingxu/Documents/GitHub/DSTPMFnewfV/formalisation/fsytxTheory.dat")
    fun find s = HOLdict.find (thydata,s)
  end
  
  fun op gcont_def _ = () val op gcont_def = TDB.find "gcont_def"
  fun op rnmap_def _ = () val op rnmap_def = TDB.find "rnmap_def"
  fun op srename_def _ = () val op srename_def = TDB.find "srename_def"
  fun op trename_def _ = () val op trename_def = TDB.find "trename_def"
  fun op frename_def _ = () val op frename_def = TDB.find "frename_def"
  fun op frpl_def _ = () val op frpl_def = TDB.find "frpl_def"
  fun op fprpl_def _ = () val op fprpl_def = TDB.find "fprpl_def"
  fun op fVinst_def _ = () val op fVinst_def = TDB.find "fVinst_def"
  fun op FALLL_def _ = () val op FALLL_def = TDB.find "FALLL_def"
  fun op wffVmap_def _ = () val op wffVmap_def = TDB.find "wffVmap_def"
  fun op finst_def _ = () val op finst_def = TDB.find "finst_def"
  fun op vinst_fVar_def _ = ()
  val op vinst_fVar_def = TDB.find "vinst_fVar_def"
  fun op wfsig_def _ = () val op wfsig_def = TDB.find "wfsig_def"
  fun op form_TY_DEF _ = () val op form_TY_DEF = TDB.find "form_TY_DEF"
  fun op form_case_def _ = ()
  val op form_case_def = TDB.find "form_case_def"
  fun op form_size_def _ = ()
  val op form_size_def = TDB.find "form_size_def"
  fun op ispsym_def _ = () val op ispsym_def = TDB.find "ispsym_def"
  fun op psymin_def _ = () val op psymin_def = TDB.find "psymin_def"
  fun op ffv_def _ = () val op ffv_def = TDB.find "ffv_def"
  fun op fabs_def _ = () val op fabs_def = TDB.find "fabs_def"
  fun op abst_def _ = () val op abst_def = TDB.find "abst_def"
  fun op mk_FALL_def _ = () val op mk_FALL_def = TDB.find "mk_FALL_def"
  fun op fbounds_def _ = () val op fbounds_def = TDB.find "fbounds_def"
  fun op fVars_def _ = () val op fVars_def = TDB.find "fVars_def"
  fun op Uof_def _ = () val op Uof_def = TDB.find "Uof_def"
  fun op ofFMAP_def _ = () val op ofFMAP_def = TDB.find "ofFMAP_def"
  fun op slfv_def _ = () val op slfv_def = TDB.find "slfv_def"
  fun op presname_def _ = () val op presname_def = TDB.find "presname_def"
  fun op vsname_def _ = () val op vsname_def = TDB.find "vsname_def"
  fun op wff_def _ = () val op wff_def = TDB.find "wff_def"
  fun op dest_eq_def_primitive _ = ()
  val op dest_eq_def_primitive = TDB.find "dest_eq_def_primitive"
  fun op is_EQ_def _ = () val op is_EQ_def = TDB.find "is_EQ_def"
  fun op EQ_def _ = () val op EQ_def = TDB.find "EQ_def"
  fun op tsname_def _ = () val op tsname_def = TDB.find "tsname_def"
  fun op sname_def _ = () val op sname_def = TDB.find "sname_def"
  fun op has_eq _ = () val op has_eq = TDB.find "has_eq"
  fun op fVslfv_def _ = () val op fVslfv_def = TDB.find "fVslfv_def"
  fun op substb_def _ = () val op substb_def = TDB.find "substb_def"
  fun op inst_eff_def _ = () val op inst_eff_def = TDB.find "inst_eff_def"
  fun op presname_rnmap _ = ()
  val op presname_rnmap = TDB.find "presname_rnmap"
  fun op tsname_trename _ = ()
  val op tsname_trename = TDB.find "tsname_trename"
  fun op frename_eq _ = () val op frename_eq = TDB.find "frename_eq"
  fun op FINITE_BIGUNION_tfv _ = ()
  val op FINITE_BIGUNION_tfv = TDB.find "FINITE_BIGUNION_tfv"
  fun op wfcod_rnmap_ffv _ = ()
  val op wfcod_rnmap_ffv = TDB.find "wfcod_rnmap_ffv"
  fun op wfcod_rnmap_cont _ = ()
  val op wfcod_rnmap_cont = TDB.find "wfcod_rnmap_cont"
  fun op wfcod_rnmap_gcont _ = ()
  val op wfcod_rnmap_gcont = TDB.find "wfcod_rnmap_gcont"
  fun op wft_trename _ = () val op wft_trename = TDB.find "wft_trename"
  fun op wfcod_rnmap_tfv _ = ()
  val op wfcod_rnmap_tfv = TDB.find "wfcod_rnmap_tfv"
  fun op gcont_SING _ = () val op gcont_SING = TDB.find "gcont_SING"
  fun op gcont_UNION _ = () val op gcont_UNION = TDB.find "gcont_UNION"
  fun op gcont_EMPTY _ = () val op gcont_EMPTY = TDB.find "gcont_EMPTY"
  fun op gcont_FINITE _ = () val op gcont_FINITE = TDB.find "gcont_FINITE"
  fun op gcont_of_cont _ = ()
  val op gcont_of_cont = TDB.find "gcont_of_cont"
  fun op gcont_is_cont _ = ()
  val op gcont_is_cont = TDB.find "gcont_is_cont"
  fun op frename_finst_ffv _ = ()
  val op frename_finst_ffv = TDB.find "frename_finst_ffv"
  fun op frename_finst _ = ()
  val op frename_finst = TDB.find "frename_finst"
  fun op frename_alt _ = () val op frename_alt = TDB.find "frename_alt"
  fun op wft_trename0 _ = () val op wft_trename0 = TDB.find "wft_trename0"
  fun op FINITE_lemma _ = () val op FINITE_lemma = TDB.find "FINITE_lemma"
  fun op wfcod_rnmap_BIGUNION _ = ()
  val op wfcod_rnmap_BIGUNION = TDB.find "wfcod_rnmap_BIGUNION"
  fun op wfcod_rnmap_SUBSET _ = ()
  val op wfcod_rnmap_SUBSET = TDB.find "wfcod_rnmap_SUBSET"
  fun op FAPPLY_rnmap_SUBSET _ = ()
  val op FAPPLY_rnmap_SUBSET = TDB.find "FAPPLY_rnmap_SUBSET"
  fun op trename_tinst_tfv _ = ()
  val op trename_tinst_tfv = TDB.find "trename_tinst_tfv"
  fun op BIGUNION_is_cont _ = ()
  val op BIGUNION_is_cont = TDB.find "BIGUNION_is_cont"
  fun op cstt_rnmap _ = () val op cstt_rnmap = TDB.find "cstt_rnmap"
  fun op no_subrename _ = () val op no_subrename = TDB.find "no_subrename"
  fun op frename_fprpl _ = ()
  val op frename_fprpl = TDB.find "frename_fprpl"
  fun op slprpl_trename _ = ()
  val op slprpl_trename = TDB.find "slprpl_trename"
  fun op trename_shift_bmap _ = ()
  val op trename_shift_bmap = TDB.find "trename_shift_bmap"
  fun op trename_tshift _ = ()
  val op trename_tshift = TDB.find "trename_tshift"
  fun op trename_tprpl _ = ()
  val op trename_tprpl = TDB.find "trename_tprpl"
  fun op ffv_frename _ = () val op ffv_frename = TDB.find "ffv_frename"
  fun op fabs_frename _ = () val op fabs_frename = TDB.find "fabs_frename"
  fun op trename_tinst _ = ()
  val op trename_tinst = TDB.find "trename_tinst"
  fun op FAPPLY_rnmap _ = () val op FAPPLY_rnmap = TDB.find "FAPPLY_rnmap"
  fun op FDOM_rnmap _ = () val op FDOM_rnmap = TDB.find "FDOM_rnmap"
  fun op trename_alt _ = () val op trename_alt = TDB.find "trename_alt"
  fun op tfv_trename _ = () val op tfv_trename = TDB.find "tfv_trename"
  fun op ok_abs_rename _ = ()
  val op ok_abs_rename = TDB.find "ok_abs_rename"
  fun op tbounds_trename _ = ()
  val op tbounds_trename = TDB.find "tbounds_trename"
  fun op TO_FMAP_SING _ = () val op TO_FMAP_SING = TDB.find "TO_FMAP_SING"
  fun op trename_fix _ = () val op trename_fix = TDB.find "trename_fix"
  fun op abssl_MAP_srename _ = ()
  val op abssl_MAP_srename = TDB.find "abssl_MAP_srename"
  fun op tabs_trename _ = () val op tabs_trename = TDB.find "tabs_trename"
  fun op tinst_cvmap_UPDATE _ = ()
  val op tinst_cvmap_UPDATE = TDB.find "tinst_cvmap_UPDATE"
  fun op wff_wfcod_cvmap_ffv _ = ()
  val op wff_wfcod_cvmap_ffv = TDB.find "wff_wfcod_cvmap_ffv"
  fun op wff_FALLL_no_vbound _ = ()
  val op wff_FALLL_no_vbound = TDB.find "wff_FALLL_no_vbound"
  fun op wff_FALLL_ffv_SUBSET _ = ()
  val op wff_FALLL_ffv_SUBSET = TDB.find "wff_FALLL_ffv_SUBSET"
  fun op wff_fVar_subst_lemma _ = ()
  val op wff_fVar_subst_lemma = TDB.find "wff_fVar_subst_lemma"
  fun op fabs_frpl _ = () val op fabs_frpl = TDB.find "fabs_frpl"
  fun op finst_TO_FMAP_id _ = ()
  val op finst_TO_FMAP_id = TDB.find "finst_TO_FMAP_id"
  fun op finst_vmap_id _ = ()
  val op finst_vmap_id = TDB.find "finst_vmap_id"
  fun op frpl_FALLL _ = () val op frpl_FALLL = TDB.find "frpl_FALLL"
  fun op fprpl_FEMPTY _ = () val op fprpl_FEMPTY = TDB.find "fprpl_FEMPTY"
  fun op frpl_fabs _ = () val op frpl_fabs = TDB.find "frpl_fabs"
  fun op fabs_fbounds_in _ = ()
  val op fabs_fbounds_in = TDB.find "fabs_fbounds_in"
  fun op fbounds_fabs_SUBSET _ = ()
  val op fbounds_fabs_SUBSET = TDB.find "fbounds_fabs_SUBSET"
  fun op shift_bmap_0_I _ = ()
  val op shift_bmap_0_I = TDB.find "shift_bmap_0_I"
  fun op mk_bmap_NIL _ = () val op mk_bmap_NIL = TDB.find "mk_bmap_NIL"
  fun op wff_FALL _ = () val op wff_FALL = TDB.find "wff_FALL"
  fun op ffv_is_cont _ = () val op ffv_is_cont = TDB.find "ffv_is_cont"
  fun op fmap_ffv_finst_eq _ = ()
  val op fmap_ffv_finst_eq = TDB.find "fmap_ffv_finst_eq"
  fun op fmap_ffv_finst_eq1 _ = ()
  val op fmap_ffv_finst_eq1 = TDB.find "fmap_ffv_finst_eq1"
  fun op fabs_id _ = () val op fabs_id = TDB.find "fabs_id"
  fun op ffv_fabs _ = () val op ffv_fabs = TDB.find "ffv_fabs"
  fun op ffv_mk_FALL _ = () val op ffv_mk_FALL = TDB.find "ffv_mk_FALL"
  fun op finst_fabs _ = () val op finst_fabs = TDB.find "finst_fabs"
  fun op ffv_finst _ = () val op ffv_finst = TDB.find "ffv_finst"
  fun op ffv_FINITE _ = () val op ffv_FINITE = TDB.find "ffv_FINITE"
  fun op NOTIN_fVslfv _ = () val op NOTIN_fVslfv = TDB.find "NOTIN_fVslfv"
  fun op Uof_UNION _ = () val op Uof_UNION = TDB.find "Uof_UNION"
  fun op Uof_Sing _ = () val op Uof_Sing = TDB.find "Uof_Sing"
  fun op Uof_INSERT _ = () val op Uof_INSERT = TDB.find "Uof_INSERT"
  fun op Uof_SUBSET_MONO _ = ()
  val op Uof_SUBSET_MONO = TDB.find "Uof_SUBSET_MONO"
  fun op Uof_EMPTY _ = () val op Uof_EMPTY = TDB.find "Uof_EMPTY"
  fun op Uof_SUBSET _ = () val op Uof_SUBSET = TDB.find "Uof_SUBSET"
  fun op fVars_finst _ = () val op fVars_finst = TDB.find "fVars_finst"
  fun op fVslfv_alt _ = () val op fVslfv_alt = TDB.find "fVslfv_alt"
  fun op fVslfv_SUBSET_ffv _ = ()
  val op fVslfv_SUBSET_ffv = TDB.find "fVslfv_SUBSET_ffv"
  fun op MEM_fVsl_SUBSET_fVslfv _ = ()
  val op MEM_fVsl_SUBSET_fVslfv = TDB.find "MEM_fVsl_SUBSET_fVslfv"
  fun op finst_EQ _ = () val op finst_EQ = TDB.find "finst_EQ"
  fun op wff_fVar _ = () val op wff_fVar = TDB.find "wff_fVar"
  fun op wff_IMP _ = () val op wff_IMP = TDB.find "wff_IMP"
  fun op wff_Pred _ = () val op wff_Pred = TDB.find "wff_Pred"
  fun op datatype_form _ = ()
  val op datatype_form = TDB.find "datatype_form"
  fun op form_11 _ = () val op form_11 = TDB.find "form_11"
  fun op form_distinct _ = ()
  val op form_distinct = TDB.find "form_distinct"
  fun op form_nchotomy _ = ()
  val op form_nchotomy = TDB.find "form_nchotomy"
  fun op form_Axiom _ = () val op form_Axiom = TDB.find "form_Axiom"
  fun op form_induction _ = ()
  val op form_induction = TDB.find "form_induction"
  fun op form_case_cong _ = ()
  val op form_case_cong = TDB.find "form_case_cong"
  fun op form_case_eq _ = () val op form_case_eq = TDB.find "form_case_eq"
  fun op ffv_thm _ = () val op ffv_thm = TDB.find "ffv_thm"
  fun op fbounds_thm _ = () val op fbounds_thm = TDB.find "fbounds_thm"
  fun op wff_finst _ = () val op wff_finst = TDB.find "wff_finst"
  fun op presname_DRESTRICT _ = ()
  val op presname_DRESTRICT = TDB.find "presname_DRESTRICT"
  fun op presname_FUPDATE _ = ()
  val op presname_FUPDATE = TDB.find "presname_FUPDATE"
  fun op ffv_EQ _ = () val op ffv_EQ = TDB.find "ffv_EQ"
  fun op wft_not_bound _ = ()
  val op wft_not_bound = TDB.find "wft_not_bound"
  fun op tsname_tinst _ = () val op tsname_tinst = TDB.find "tsname_tinst"
  fun op wff_EQ _ = () val op wff_EQ = TDB.find "wff_EQ"
  fun op wff_False _ = () val op wff_False = TDB.find "wff_False"
  fun op wff_cases _ = () val op wff_cases = TDB.find "wff_cases"
  fun op wff_strongind _ = ()
  val op wff_strongind = TDB.find "wff_strongind"
  fun op wff_ind _ = () val op wff_ind = TDB.find "wff_ind"
  fun op wff_rules _ = () val op wff_rules = TDB.find "wff_rules"
  fun op dest_eq_def _ = () val op dest_eq_def = TDB.find "dest_eq_def"
  fun op dest_eq_ind _ = () val op dest_eq_ind = TDB.find "dest_eq_ind"
  fun op IN_fVslfv _ = () val op IN_fVslfv = TDB.find "IN_fVslfv"
  fun op IN_slfv _ = () val op IN_slfv = TDB.find "IN_slfv"
  fun op fbounds_fabs _ = () val op fbounds_fabs = TDB.find "fbounds_fabs"
  fun op ffv_fabs_fVslfv _ = ()
  val op ffv_fabs_fVslfv = TDB.find "ffv_fabs_fVslfv"
  fun op wff_wfs _ = () val op wff_wfs = TDB.find "wff_wfs"
  fun op fbounds_fabs_fVslfv _ = ()
  val op fbounds_fabs_fVslfv = TDB.find "fbounds_fabs_fVslfv"
  fun op wff_fbounds _ = () val op wff_fbounds = TDB.find "wff_fbounds"
  fun op fprpl_mk_bmap_CONS _ = ()
  val op fprpl_mk_bmap_CONS = TDB.find "fprpl_mk_bmap_CONS"
  fun op slprpl_mk_bmap_CONS _ = ()
  val op slprpl_mk_bmap_CONS = TDB.find "slprpl_mk_bmap_CONS"
  fun op tprpl_mk_bmap_CONS _ = ()
  val op tprpl_mk_bmap_CONS = TDB.find "tprpl_mk_bmap_CONS"
  fun op sfv_ffv _ = () val op sfv_ffv = TDB.find "sfv_ffv"
  fun op ffv_fprpl _ = () val op ffv_fprpl = TDB.find "ffv_fprpl"
  fun op fprpl_mk_bmap_abs _ = ()
  val op fprpl_mk_bmap_abs = TDB.find "fprpl_mk_bmap_abs"
  fun op wff_spec _ = () val op wff_spec = TDB.find "wff_spec"
  fun op presname_cvmap _ = ()
  val op presname_cvmap = TDB.find "presname_cvmap"
  fun op wff_no_vbound _ = ()
  val op wff_no_vbound = TDB.find "wff_no_vbound"
  fun op wft_no_vbound _ = ()
  val op wft_no_vbound = TDB.find "wft_no_vbound"
  fun op ffv_mk_FALL_fVslfv _ = ()
  val op ffv_mk_FALL_fVslfv = TDB.find "ffv_mk_FALL_fVslfv"
  fun op finst_eq_cvmap _ = ()
  val op finst_eq_cvmap = TDB.find "finst_eq_cvmap"
  fun op wff_frename _ = () val op wff_frename = TDB.find "wff_frename"
  fun op mk_FALL_rename_eq _ = ()
  val op mk_FALL_rename_eq = TDB.find "mk_FALL_rename_eq"
  fun op frename_fix _ = () val op frename_fix = TDB.find "frename_fix"
  fun op ffv_fabs_SUBSET _ = ()
  val op ffv_fabs_SUBSET = TDB.find "ffv_fabs_SUBSET"
  fun op IN_tfv_trename _ = ()
  val op IN_tfv_trename = TDB.find "IN_tfv_trename"
  fun op trename_back _ = () val op trename_back = TDB.find "trename_back"
  fun op tprpl_FMAP_MAP_tabs_IN _ = ()
  val op tprpl_FMAP_MAP_tabs_IN = TDB.find "tprpl_FMAP_MAP_tabs_IN"
  fun op slprpl_FMAP_MAP_abssl_IN _ = ()
  val op slprpl_FMAP_MAP_abssl_IN = TDB.find "slprpl_FMAP_MAP_abssl_IN"
  fun op fprpl_FMAP_MAP_fabs_IN _ = ()
  val op fprpl_FMAP_MAP_fabs_IN = TDB.find "fprpl_FMAP_MAP_fabs_IN"
  fun op NOTIN_trename _ = ()
  val op NOTIN_trename = TDB.find "NOTIN_trename"
  fun op NOTIN_frename _ = ()
  val op NOTIN_frename = TDB.find "NOTIN_frename"
  fun op frename_FALLL _ = ()
  val op frename_FALLL = TDB.find "frename_FALLL"
  fun op ffv_FALLL _ = () val op ffv_FALLL = TDB.find "ffv_FALLL"
  fun op BIGUNION_IMAGE_sbounds_tfv _ = ()
  val op BIGUNION_IMAGE_sbounds_tfv = TDB.find "BIGUNION_IMAGE_sbounds_tfv"
  fun op BIGUNION_IMAGE_sbounds_ffv _ = ()
  val op BIGUNION_IMAGE_sbounds_ffv = TDB.find "BIGUNION_IMAGE_sbounds_ffv"
  fun op fresh_name_ex _ = ()
  val op fresh_name_ex = TDB.find "fresh_name_ex"
  fun op inst_eff_tinst _ = ()
  val op inst_eff_tinst = TDB.find "inst_eff_tinst"
  fun op cstt_EXT _ = () val op cstt_EXT = TDB.find "cstt_EXT"
  fun op ill_formed_fabs_still_in _ = ()
  val op ill_formed_fabs_still_in = TDB.find "ill_formed_fabs_still_in"
  
  
val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "fsytx"

val fsytx_grammars = valOf (Parse.grammarDB {thyname = "fsytx"})
end
