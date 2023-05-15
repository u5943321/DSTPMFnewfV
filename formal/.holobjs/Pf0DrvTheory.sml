structure Pf0DrvTheory :> Pf0DrvTheory =
struct
  
  val _ = if !Globals.print_thy_loads
    then TextIO.print "Loading Pf0DrvTheory ... "
    else ()
  
  open Type Term Thm
  local open PfDrvTheory in end;
  
  structure TDB = struct
    val thydata = 
      TheoryReader.load_thydata "Pf0Drv"
        (holpathdb.subst_pathvars "/Users/yimingxu/Documents/GitHub/DSTPMFnewfV/formal/Pf0DrvTheory.dat")
    fun find s = HOLdict.find (thydata,s)
  end
  
  fun op Pf0_def _ = () val op Pf0_def = TDB.find "Pf0_def"
  fun op Pf0Drv_def _ = () val op Pf0Drv_def = TDB.find "Pf0Drv_def"
  fun op wfaths_def _ = () val op wfaths_def = TDB.find "wfaths_def"
  fun op wfsigaths_def _ = ()
  val op wfsigaths_def = TDB.find "wfsigaths_def"
  fun op dest_forall_def _ = ()
  val op dest_forall_def = TDB.find "dest_forall_def"
  fun op is_fall_def_primitive _ = ()
  val op is_fall_def_primitive = TDB.find "is_fall_def_primitive"
  fun op Pf0Drv_double_neg _ = ()
  val op Pf0Drv_double_neg = TDB.find "Pf0Drv_double_neg"
  fun op Pf0Drv_add_cont _ = ()
  val op Pf0Drv_add_cont = TDB.find "Pf0Drv_add_cont"
  fun op Pf0Drv_add_cont0 _ = ()
  val op Pf0Drv_add_cont0 = TDB.find "Pf0Drv_add_cont0"
  fun op Pf0Drv_add_cont1 _ = ()
  val op Pf0Drv_add_cont1 = TDB.find "Pf0Drv_add_cont1"
  fun op Pf0Drv_undisch _ = ()
  val op Pf0Drv_undisch = TDB.find "Pf0Drv_undisch"
  fun op Pf0_rules _ = () val op Pf0_rules = TDB.find "Pf0_rules"
  fun op Pf0_ind _ = () val op Pf0_ind = TDB.find "Pf0_ind"
  fun op Pf0_strongind _ = ()
  val op Pf0_strongind = TDB.find "Pf0_strongind"
  fun op Pf0_cases _ = () val op Pf0_cases = TDB.find "Pf0_cases"
  fun op Pf0_AX _ = () val op Pf0_AX = TDB.find "Pf0_AX"
  fun op Pf0_cong _ = () val op Pf0_cong = TDB.find "Pf0_cong"
  fun op Pf0_vinsth _ = () val op Pf0_vinsth = TDB.find "Pf0_vinsth"
  fun op Pf0_ALLI _ = () val op Pf0_ALLI = TDB.find "Pf0_ALLI"
  fun op Pf0_ALLE _ = () val op Pf0_ALLE = TDB.find "Pf0_ALLE"
  fun op Pf0_double_neg _ = ()
  val op Pf0_double_neg = TDB.find "Pf0_double_neg"
  fun op Pf0_fromBot _ = () val op Pf0_fromBot = TDB.find "Pf0_fromBot"
  fun op Pf0_assume _ = () val op Pf0_assume = TDB.find "Pf0_assume"
  fun op Pf0_mp _ = () val op Pf0_mp = TDB.find "Pf0_mp"
  fun op Pf0_disch _ = () val op Pf0_disch = TDB.find "Pf0_disch"
  fun op Pf0_refl _ = () val op Pf0_refl = TDB.find "Pf0_refl"
  fun op Pf0_sym _ = () val op Pf0_sym = TDB.find "Pf0_sym"
  fun op Pf0_trans _ = () val op Pf0_trans = TDB.find "Pf0_trans"
  fun op Pf0_add_cont1 _ = ()
  val op Pf0_add_cont1 = TDB.find "Pf0_add_cont1"
  fun op Pf0_cont_is_cont _ = ()
  val op Pf0_cont_is_cont = TDB.find "Pf0_cont_is_cont"
  fun op is_cfm_IFF _ = () val op is_cfm_IFF = TDB.find "is_cfm_IFF"
  fun op is_cfm_fprpl _ = () val op is_cfm_fprpl = TDB.find "is_cfm_fprpl"
  fun op is_cfm_finst _ = () val op is_cfm_finst = TDB.find "is_cfm_finst"
  fun op is_cfm_fabs _ = () val op is_cfm_fabs = TDB.find "is_cfm_fabs"
  fun op is_cfm_frpl _ = () val op is_cfm_frpl = TDB.find "is_cfm_frpl"
  fun op is_cfm_NEG _ = () val op is_cfm_NEG = TDB.find "is_cfm_NEG"
  fun op is_cfm_EQ _ = () val op is_cfm_EQ = TDB.find "is_cfm_EQ"
  fun op Pf0_cfm _ = () val op Pf0_cfm = TDB.find "Pf0_cfm"
  fun op Pf0Drv_cfm _ = () val op Pf0Drv_cfm = TDB.find "Pf0Drv_cfm"
  fun op Pf0Drv_cont_wf _ = ()
  val op Pf0Drv_cont_wf = TDB.find "Pf0Drv_cont_wf"
  fun op mk_bmap_BIGUNION _ = ()
  val op mk_bmap_BIGUNION = TDB.find "mk_bmap_BIGUNION"
  fun op FAPPLY_mk_bmap_REVERSE_Lofeqthl _ = ()
  val op FAPPLY_mk_bmap_REVERSE_Lofeqthl = TDB.find
    "FAPPLY_mk_bmap_REVERSE_Lofeqthl"
  fun op FAPPLY_mk_bmap_REVERSE_Rofeqthl _ = ()
  val op FAPPLY_mk_bmap_REVERSE_Rofeqthl = TDB.find
    "FAPPLY_mk_bmap_REVERSE_Rofeqthl"
  fun op EL_Lofeqthl _ = () val op EL_Lofeqthl = TDB.find "EL_Lofeqthl"
  fun op EL_Rofeqthl _ = () val op EL_Rofeqthl = TDB.find "EL_Rofeqthl"
  fun op Pf0_ffv_SUBSET_wff _ = ()
  val op Pf0_ffv_SUBSET_wff = TDB.find "Pf0_ffv_SUBSET_wff"
  fun op Pf0_wff _ = () val op Pf0_wff = TDB.find "Pf0_wff"
  fun op Pf0Drv_wff _ = () val op Pf0Drv_wff = TDB.find "Pf0Drv_wff"
  fun op Pf0Drv_ffv_SUBSET_cont _ = ()
  val op Pf0Drv_ffv_SUBSET_cont = TDB.find "Pf0Drv_ffv_SUBSET_cont"
  fun op Pf0Drv_concl_ffv_SUBSET _ = ()
  val op Pf0Drv_concl_ffv_SUBSET = TDB.find "Pf0Drv_concl_ffv_SUBSET"
  fun op Pf0Drv_assum_ffv_SUBSET _ = ()
  val op Pf0Drv_assum_ffv_SUBSET = TDB.find "Pf0Drv_assum_ffv_SUBSET"
  fun op Pf0Drv_assume _ = ()
  val op Pf0Drv_assume = TDB.find "Pf0Drv_assume"
  fun op Pf0Drv_mp _ = () val op Pf0Drv_mp = TDB.find "Pf0Drv_mp"
  fun op Pf0Drv_disch _ = () val op Pf0Drv_disch = TDB.find "Pf0Drv_disch"
  fun op Pf0Drv_add_assum _ = ()
  val op Pf0Drv_add_assum = TDB.find "Pf0Drv_add_assum"
  fun op Pf0Drv_wff1 _ = () val op Pf0Drv_wff1 = TDB.find "Pf0Drv_wff1"
  fun op Pf0Drv_cont_SUBSET _ = ()
  val op Pf0Drv_cont_SUBSET = TDB.find "Pf0Drv_cont_SUBSET"
  fun op Pf0Drv_assum_SUBSET _ = ()
  val op Pf0Drv_assum_SUBSET = TDB.find "Pf0Drv_assum_SUBSET"
  fun op Pf0Drv_gen _ = () val op Pf0Drv_gen = TDB.find "Pf0Drv_gen"
  fun op Pf0Drv_cont_wf' _ = ()
  val op Pf0Drv_cont_wf' = TDB.find "Pf0Drv_cont_wf'"
  fun op is_fall_ind _ = () val op is_fall_ind = TDB.find "is_fall_ind"
  fun op is_fall_def _ = () val op is_fall_def = TDB.find "is_fall_def"
  fun op Pf0Drv_spec _ = () val op Pf0Drv_spec = TDB.find "Pf0Drv_spec"
  fun op Pf0Drv_fromBot _ = ()
  val op Pf0Drv_fromBot = TDB.find "Pf0Drv_fromBot"
  fun op Pf0Drv_refl _ = () val op Pf0Drv_refl = TDB.find "Pf0Drv_refl"
  fun op Pf0Drv_sym _ = () val op Pf0Drv_sym = TDB.find "Pf0Drv_sym"
  fun op Pf0Drv_trans _ = () val op Pf0Drv_trans = TDB.find "Pf0Drv_trans"
  fun op Pf0Drv_cong _ = () val op Pf0Drv_cong = TDB.find "Pf0Drv_cong"
  
  
val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "Pf0Drv"

val Pf0Drv_grammars = valOf (Parse.grammarDB {thyname = "Pf0Drv"})
end
