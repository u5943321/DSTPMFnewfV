structure PfDrvTheory :> PfDrvTheory =
struct
  
  val _ = if !Globals.print_thy_loads
    then TextIO.print "Loading PfDrvTheory ... "
    else ()
  
  open Type Term Thm
  local open newdefsTheory in end;
  
  structure TDB = struct
    val thydata = 
      TheoryReader.load_thydata "PfDrv"
        (holpathdb.subst_pathvars "/Users/yimingxu/Documents/GitHub/DSTPMFnewfV/formal/PfDrvTheory.dat")
    fun find s = HOLdict.find (thydata,s)
  end
  
  fun op Leq_def _ = () val op Leq_def = TDB.find "Leq_def"
  fun op Req_def _ = () val op Req_def = TDB.find "Req_def"
  fun op Pf_def _ = () val op Pf_def = TDB.find "Pf_def"
  fun op wfsigaxs_def _ = () val op wfsigaxs_def = TDB.find "wfsigaxs_def"
  fun op PfDrv_def _ = () val op PfDrv_def = TDB.find "PfDrv_def"
  fun op PfDrv_double_neg _ = ()
  val op PfDrv_double_neg = TDB.find "PfDrv_double_neg"
  fun op PfDrv_add_cont _ = ()
  val op PfDrv_add_cont = TDB.find "PfDrv_add_cont"
  fun op PfDrv_add_cont0 _ = ()
  val op PfDrv_add_cont0 = TDB.find "PfDrv_add_cont0"
  fun op PfDrv_add_cont1 _ = ()
  val op PfDrv_add_cont1 = TDB.find "PfDrv_add_cont1"
  fun op PfDrv_undisch _ = ()
  val op PfDrv_undisch = TDB.find "PfDrv_undisch"
  fun op Pf_rules _ = () val op Pf_rules = TDB.find "Pf_rules"
  fun op Pf_ind _ = () val op Pf_ind = TDB.find "Pf_ind"
  fun op Pf_strongind _ = () val op Pf_strongind = TDB.find "Pf_strongind"
  fun op Pf_cases _ = () val op Pf_cases = TDB.find "Pf_cases"
  fun op Pf_AX _ = () val op Pf_AX = TDB.find "Pf_AX"
  fun op Pf_fVcong _ = () val op Pf_fVcong = TDB.find "Pf_fVcong"
  fun op Pf_fVinsth _ = () val op Pf_fVinsth = TDB.find "Pf_fVinsth"
  fun op Pf_vinsth _ = () val op Pf_vinsth = TDB.find "Pf_vinsth"
  fun op Pf_ALLI _ = () val op Pf_ALLI = TDB.find "Pf_ALLI"
  fun op Pf_ALLE _ = () val op Pf_ALLE = TDB.find "Pf_ALLE"
  fun op Pf_double_neg _ = ()
  val op Pf_double_neg = TDB.find "Pf_double_neg"
  fun op Pf_fromBot _ = () val op Pf_fromBot = TDB.find "Pf_fromBot"
  fun op Pf_assume _ = () val op Pf_assume = TDB.find "Pf_assume"
  fun op Pf_mp _ = () val op Pf_mp = TDB.find "Pf_mp"
  fun op Pf_disch _ = () val op Pf_disch = TDB.find "Pf_disch"
  fun op Pf_refl _ = () val op Pf_refl = TDB.find "Pf_refl"
  fun op Pf_sym _ = () val op Pf_sym = TDB.find "Pf_sym"
  fun op Pf_trans _ = () val op Pf_trans = TDB.find "Pf_trans"
  fun op Pf_add_cont1 _ = () val op Pf_add_cont1 = TDB.find "Pf_add_cont1"
  fun op Pf_cont_is_cont _ = ()
  val op Pf_cont_is_cont = TDB.find "Pf_cont_is_cont"
  fun op PfDrv_cont_wf _ = ()
  val op PfDrv_cont_wf = TDB.find "PfDrv_cont_wf"
  fun op Leq_Req_EQ _ = () val op Leq_Req_EQ = TDB.find "Leq_Req_EQ"
  fun op wfabsap_wfs _ = () val op wfabsap_wfs = TDB.find "wfabsap_wfs"
  fun op is_EQ_wff_Leq_Req _ = ()
  val op is_EQ_wff_Leq_Req = TDB.find "is_EQ_wff_Leq_Req"
  fun op wff_IFF _ = () val op wff_IFF = TDB.find "wff_IFF"
  fun op wff_fVar' _ = () val op wff_fVar' = TDB.find "wff_fVar'"
  fun op wff_False' _ = () val op wff_False' = TDB.find "wff_False'"
  fun op wff_NEG _ = () val op wff_NEG = TDB.find "wff_NEG"
  fun op Pf_ffv_SUBSET_wff _ = ()
  val op Pf_ffv_SUBSET_wff = TDB.find "Pf_ffv_SUBSET_wff"
  fun op Pf_wff _ = () val op Pf_wff = TDB.find "Pf_wff"
  fun op PfDrv_wff _ = () val op PfDrv_wff = TDB.find "PfDrv_wff"
  fun op PfDrv_ffv_SUBSET_cont _ = ()
  val op PfDrv_ffv_SUBSET_cont = TDB.find "PfDrv_ffv_SUBSET_cont"
  fun op PfDrv_concl_ffv_SUBSET _ = ()
  val op PfDrv_concl_ffv_SUBSET = TDB.find "PfDrv_concl_ffv_SUBSET"
  fun op PfDrv_assum_ffv_SUBSET _ = ()
  val op PfDrv_assum_ffv_SUBSET = TDB.find "PfDrv_assum_ffv_SUBSET"
  fun op PfDrv_assume _ = () val op PfDrv_assume = TDB.find "PfDrv_assume"
  fun op PfDrv_mp _ = () val op PfDrv_mp = TDB.find "PfDrv_mp"
  fun op PfDrv_disch _ = () val op PfDrv_disch = TDB.find "PfDrv_disch"
  fun op PfDrv_add_assum _ = ()
  val op PfDrv_add_assum = TDB.find "PfDrv_add_assum"
  fun op PfDrv_wff1 _ = () val op PfDrv_wff1 = TDB.find "PfDrv_wff1"
  fun op PfDrv_contrapos0 _ = ()
  val op PfDrv_contrapos0 = TDB.find "PfDrv_contrapos0"
  fun op PfDrv_contrapos _ = ()
  val op PfDrv_contrapos = TDB.find "PfDrv_contrapos"
  fun op fVslfv_IMP _ = () val op fVslfv_IMP = TDB.find "fVslfv_IMP"
  fun op fVslfv_False _ = () val op fVslfv_False = TDB.find "fVslfv_False"
  fun op wff_FALL_EX _ = () val op wff_FALL_EX = TDB.find "wff_FALL_EX"
  fun op PfDrv_cont_SUBSET _ = ()
  val op PfDrv_cont_SUBSET = TDB.find "PfDrv_cont_SUBSET"
  fun op PfDrv_assum_SUBSET _ = ()
  val op PfDrv_assum_SUBSET = TDB.find "PfDrv_assum_SUBSET"
  fun op PfDrv_gen _ = () val op PfDrv_gen = TDB.find "PfDrv_gen"
  fun op ffv_EX _ = () val op ffv_EX = TDB.find "ffv_EX"
  fun op PfDrv_cont_wf' _ = ()
  val op PfDrv_cont_wf' = TDB.find "PfDrv_cont_wf'"
  fun op fVars_NEG _ = () val op fVars_NEG = TDB.find "fVars_NEG"
  fun op fVars_frpl _ = () val op fVars_frpl = TDB.find "fVars_frpl"
  fun op Uof_sfv_SUBSET_cont _ = ()
  val op Uof_sfv_SUBSET_cont = TDB.find "Uof_sfv_SUBSET_cont"
  fun op PfDrv_EX_E _ = () val op PfDrv_EX_E = TDB.find "PfDrv_EX_E"
  fun op PfDrv_concl_wff _ = ()
  val op PfDrv_concl_wff = TDB.find "PfDrv_concl_wff"
  fun op PfDrv_assum_wff _ = ()
  val op PfDrv_assum_wff = TDB.find "PfDrv_assum_wff"
  fun op PfDrv_thfVars_wffV _ = ()
  val op PfDrv_thfVars_wffV = TDB.find "PfDrv_thfVars_wffV"
  fun op PfDrv_fVinsth _ = ()
  val op PfDrv_fVinsth = TDB.find "PfDrv_fVinsth"
  fun op Uof_FINITE_lemma _ = ()
  val op Uof_FINITE_lemma = TDB.find "Uof_FINITE_lemma"
  fun op PfDrv_assum_FINITE _ = ()
  val op PfDrv_assum_FINITE = TDB.find "PfDrv_assum_FINITE"
  fun op fVars_FINITE _ = () val op fVars_FINITE = TDB.find "fVars_FINITE"
  fun op PfDrv_thfVars_FINITE _ = ()
  val op PfDrv_thfVars_FINITE = TDB.find "PfDrv_thfVars_FINITE"
  
  
val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "PfDrv"

val PfDrv_grammars = valOf (Parse.grammarDB {thyname = "PfDrv"})
end
