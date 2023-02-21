structure newdefsTheory :> newdefsTheory =
struct
  
  val _ = if !Globals.print_thy_loads
    then TextIO.print "Loading newdefsTheory ... "
    else ()
  
  open Type Term Thm
  local open fVinstTheory in end;
  
  structure TDB = struct
    val thydata = 
      TheoryReader.load_thydata "newdefs"
        (holpathdb.subst_pathvars "/Users/yimingxu/Documents/GitHub/DSTPMFnewfV/formalisation/newdefsTheory.dat")
    fun find s = HOLdict.find (thydata,s)
  end
  
  fun op cont_def _ = () val op cont_def = TDB.find "cont_def"
  fun op assum_def _ = () val op assum_def = TDB.find "assum_def"
  fun op concl_def _ = () val op concl_def = TDB.find "concl_def"
  fun op thfVars_def _ = () val op thfVars_def = TDB.find "thfVars_def"
  fun op genavds_def _ = () val op genavds_def = TDB.find "genavds_def"
  fun op map2list _ = () val op map2list = TDB.find "map2list"
  fun op Lofeqths_def _ = () val op Lofeqths_def = TDB.find "Lofeqths_def"
  fun op Rofeqths_def _ = () val op Rofeqths_def = TDB.find "Rofeqths_def"
  fun op NEG_def _ = () val op NEG_def = TDB.find "NEG_def"
  fun op DISJ_def _ = () val op DISJ_def = TDB.find "DISJ_def"
  fun op CONJ_def _ = () val op CONJ_def = TDB.find "CONJ_def"
  fun op True_def _ = () val op True_def = TDB.find "True_def"
  fun op IFF_def _ = () val op IFF_def = TDB.find "IFF_def"
  fun op EX_def _ = () val op EX_def = TDB.find "EX_def"
  fun op vinst_cont_def _ = ()
  val op vinst_cont_def = TDB.find "vinst_cont_def"
  fun op vinsth_def _ = () val op vinsth_def = TDB.find "vinsth_def"
  fun op fVinsth_def _ = () val op fVinsth_def = TDB.find "fVinsth_def"
  fun op insth_def _ = () val op insth_def = TDB.find "insth_def"
  fun op instf_def _ = () val op instf_def = TDB.find "instf_def"
  fun op is_cfm_def _ = () val op is_cfm_def = TDB.find "is_cfm_def"
  fun op is_cth _ = () val op is_cth = TDB.find "is_cth"
  fun op cfVmap_def _ = () val op cfVmap_def = TDB.find "cfVmap_def"
  fun op wfcfVmap_def _ = () val op wfcfVmap_def = TDB.find "wfcfVmap_def"
  fun op wfvmap_def _ = () val op wfvmap_def = TDB.find "wfvmap_def"
  fun op gen_def _ = () val op gen_def = TDB.find "gen_def"
  fun op assume_def _ = () val op assume_def = TDB.find "assume_def"
  fun op refl_def _ = () val op refl_def = TDB.find "refl_def"
  fun op sym_def_primitive _ = ()
  val op sym_def_primitive = TDB.find "sym_def_primitive"
  fun op disch_def _ = () val op disch_def = TDB.find "disch_def"
  fun op fVcong_def _ = () val op fVcong_def = TDB.find "fVcong_def"
  fun op fcong_def _ = () val op fcong_def = TDB.find "fcong_def"
  fun op add_assum_def _ = ()
  val op add_assum_def = TDB.find "add_assum_def"
  fun op add_cont_def _ = () val op add_cont_def = TDB.find "add_cont_def"
  fun op add_cont1_def _ = ()
  val op add_cont1_def = TDB.find "add_cont1_def"
  fun op undisch_def_primitive _ = ()
  val op undisch_def_primitive = TDB.find "undisch_def_primitive"
  fun op uniqifn_def _ = () val op uniqifn_def = TDB.find "uniqifn_def"
  fun op alluniq_def _ = () val op alluniq_def = TDB.find "alluniq_def"
  fun op ffVrn_def _ = () val op ffVrn_def = TDB.find "ffVrn_def"
  fun op fVrn_def _ = () val op fVrn_def = TDB.find "fVrn_def"
  fun op vinst_bmap_def _ = ()
  val op vinst_bmap_def = TDB.find "vinst_bmap_def"
  fun op vinst_fVmap_def _ = ()
  val op vinst_fVmap_def = TDB.find "vinst_fVmap_def"
  fun op o_fVmap_def _ = () val op o_fVmap_def = TDB.find "o_fVmap_def"
  fun op subfm_def _ = () val op subfm_def = TDB.find "subfm_def"
  fun op vsfv_def _ = () val op vsfv_def = TDB.find "vsfv_def"
  fun op wffsig_def _ = () val op wffsig_def = TDB.find "wffsig_def"
  fun op absapLs_def _ = () val op absapLs_def = TDB.find "absapLs_def"
  fun op fVmap_fVrn_def _ = ()
  val op fVmap_fVrn_def = TDB.find "fVmap_fVrn_def"
  fun op plainfV_def _ = () val op plainfV_def = TDB.find "plainfV_def"
  fun op rn2fVmap_def _ = () val op rn2fVmap_def = TDB.find "rn2fVmap_def"
  fun op map2list_compute _ = ()
  val op map2list_compute = TDB.find "map2list_compute"
  fun op ffv_IFF _ = () val op ffv_IFF = TDB.find "ffv_IFF"
  fun op spec_ind _ = () val op spec_ind = TDB.find "spec_ind"
  fun op spec_def _ = () val op spec_def = TDB.find "spec_def"
  fun op sym_ind _ = () val op sym_ind = TDB.find "sym_ind"
  fun op sym_def _ = () val op sym_def = TDB.find "sym_def"
  fun op add_assum_EMPTY _ = ()
  val op add_assum_EMPTY = TDB.find "add_assum_EMPTY"
  fun op undisch_ind _ = () val op undisch_ind = TDB.find "undisch_ind"
  fun op undisch_def _ = () val op undisch_def = TDB.find "undisch_def"
  fun op is_cont_DELETE _ = ()
  val op is_cont_DELETE = TDB.find "is_cont_DELETE"
  fun op EMPTY_is_cont _ = ()
  val op EMPTY_is_cont = TDB.find "EMPTY_is_cont"
  fun op add_cont_EMPTY _ = ()
  val op add_cont_EMPTY = TDB.find "add_cont_EMPTY"
  fun op cont_decompose _ = ()
  val op cont_decompose = TDB.find "cont_decompose"
  fun op add_cont_UNION _ = ()
  val op add_cont_UNION = TDB.find "add_cont_UNION"
  fun op add_cont1_add_cont _ = ()
  val op add_cont1_add_cont = TDB.find "add_cont1_add_cont"
  fun op BIGUNION_IMAGE_Uof _ = ()
  val op BIGUNION_IMAGE_Uof = TDB.find "BIGUNION_IMAGE_Uof"
  fun op LENGTH_map2list _ = ()
  val op LENGTH_map2list = TDB.find "LENGTH_map2list"
  fun op EL_map2list _ = () val op EL_map2list = TDB.find "EL_map2list"
  fun op LENGTH_LRofeqthl _ = ()
  val op LENGTH_LRofeqthl = TDB.find "LENGTH_LRofeqthl"
  fun op ffv_NEG _ = () val op ffv_NEG = TDB.find "ffv_NEG"
  fun op Uof_lemma_classic _ = ()
  val op Uof_lemma_classic = TDB.find "Uof_lemma_classic"
  fun op wfabsap_Lofeqthl_sl_NONNIL _ = ()
  val op wfabsap_Lofeqthl_sl_NONNIL = TDB.find "wfabsap_Lofeqthl_sl_NONNIL"
  fun op MEM_map2list _ = () val op MEM_map2list = TDB.find "MEM_map2list"
  fun op dest_eq_EQ _ = () val op dest_eq_EQ = TDB.find "dest_eq_EQ"
  fun op MEM_Lofeqthl_map2list _ = ()
  val op MEM_Lofeqthl_map2list = TDB.find "MEM_Lofeqthl_map2list"
  fun op MEM_Rofeqthl_map2list _ = ()
  val op MEM_Rofeqthl_map2list = TDB.find "MEM_Rofeqthl_map2list"
  fun op IN_Uof _ = () val op IN_Uof = TDB.find "IN_Uof"
  fun op fVars_vinst _ = () val op fVars_vinst = TDB.find "fVars_vinst"
  fun op instf_fVinst_finst _ = ()
  val op instf_fVinst_finst = TDB.find "instf_fVinst_finst"
  fun op insth_instf _ = () val op insth_instf = TDB.find "insth_instf"
  fun op vinst_cont_EMPTY _ = ()
  val op vinst_cont_EMPTY = TDB.find "vinst_cont_EMPTY"
  fun op vinst_cont_UNION _ = ()
  val op vinst_cont_UNION = TDB.find "vinst_cont_UNION"
  fun op alluniq_EMPTY _ = ()
  val op alluniq_EMPTY = TDB.find "alluniq_EMPTY"
  fun op uniqifn_SUBSET _ = ()
  val op uniqifn_SUBSET = TDB.find "uniqifn_SUBSET"
  fun op fVars_ffVrn _ = () val op fVars_ffVrn = TDB.find "fVars_ffVrn"
  fun op uniqifn_alluniq0 _ = ()
  val op uniqifn_alluniq0 = TDB.find "uniqifn_alluniq0"
  fun op uniqifn_alluniq _ = ()
  val op uniqifn_alluniq = TDB.find "uniqifn_alluniq"
  fun op FDOM_vinst_bmap _ = ()
  val op FDOM_vinst_bmap = TDB.find "FDOM_vinst_bmap"
  fun op FAPPLY_vinst_bmap _ = ()
  val op FAPPLY_vinst_bmap = TDB.find "FAPPLY_vinst_bmap"
  fun op tinst_tprpl _ = () val op tinst_tprpl = TDB.find "tinst_tprpl"
  fun op tshift_tinst _ = () val op tshift_tinst = TDB.find "tshift_tinst"
  fun op shift_bmap_vinst_bmap _ = ()
  val op shift_bmap_vinst_bmap = TDB.find "shift_bmap_vinst_bmap"
  fun op finst_fprpl _ = () val op finst_fprpl = TDB.find "finst_fprpl"
  fun op vinst_bmap_alt _ = ()
  val op vinst_bmap_alt = TDB.find "vinst_bmap_alt"
  fun op FDOM_vinst_fVmap _ = ()
  val op FDOM_vinst_fVmap = TDB.find "FDOM_vinst_fVmap"
  fun op FAPPLY_vinst_fVmap _ = ()
  val op FAPPLY_vinst_fVmap = TDB.find "FAPPLY_vinst_fVmap"
  fun op instf_fVinst _ = () val op instf_fVinst = TDB.find "instf_fVinst"
  fun op FDOM_o_fVmap _ = () val op FDOM_o_fVmap = TDB.find "FDOM_o_fVmap"
  fun op FAPPLY_o_fVmap _ = ()
  val op FAPPLY_o_fVmap = TDB.find "FAPPLY_o_fVmap"
  fun op FAPPLY_o_fVmap1 _ = ()
  val op FAPPLY_o_fVmap1 = TDB.find "FAPPLY_o_fVmap1"
  fun op FAPPLY_o_fVmap2 _ = ()
  val op FAPPLY_o_fVmap2 = TDB.find "FAPPLY_o_fVmap2"
  fun op FALLL_components _ = ()
  val op FALLL_components = TDB.find "FALLL_components"
  fun op wff_FALL_alt _ = () val op wff_FALL_alt = TDB.find "wff_FALL_alt"
  fun op fVslfv_fabs _ = () val op fVslfv_fabs = TDB.find "fVslfv_fabs"
  fun op FALLL_fbounds _ = ()
  val op FALLL_fbounds = TDB.find "FALLL_fbounds"
  fun op fVinst_fprpl _ = () val op fVinst_fprpl = TDB.find "fVinst_fprpl"
  fun op absapLs_fabs _ = () val op absapLs_fabs = TDB.find "absapLs_fabs"
  fun op wff_absapLs_eq _ = ()
  val op wff_absapLs_eq = TDB.find "wff_absapLs_eq"
  fun op fVar_subfm_IN_absapLs _ = ()
  val op fVar_subfm_IN_absapLs = TDB.find "fVar_subfm_IN_absapLs"
  fun op wff_subfm_fVar_LENGTH _ = ()
  val op wff_subfm_fVar_LENGTH = TDB.find "wff_subfm_fVar_LENGTH"
  fun op fVar_FALLL_inc _ = ()
  val op fVar_FALLL_inc = TDB.find "fVar_FALLL_inc"
  fun op fVar_prpl_o_fVmap _ = ()
  val op fVar_prpl_o_fVmap = TDB.find "fVar_prpl_o_fVmap"
  fun op fVar_prpl_o_fVmap1 _ = ()
  val op fVar_prpl_o_fVmap1 = TDB.find "fVar_prpl_o_fVmap1"
  fun op ofFMAP_SUBSET_MONO _ = ()
  val op ofFMAP_SUBSET_MONO = TDB.find "ofFMAP_SUBSET_MONO"
  fun op ffv_finst_wfvmap _ = ()
  val op ffv_finst_wfvmap = TDB.find "ffv_finst_wfvmap"
  fun op IN_vsfv _ = () val op IN_vsfv = TDB.find "IN_vsfv"
  fun op IN_Uof_Uof _ = () val op IN_Uof_Uof = TDB.find "IN_Uof_Uof"
  fun op IN_genavds _ = () val op IN_genavds = TDB.find "IN_genavds"
  fun op NOTIN_genavds _ = ()
  val op NOTIN_genavds = TDB.find "NOTIN_genavds"
  fun op trpl_tprpl _ = () val op trpl_tprpl = TDB.find "trpl_tprpl"
  fun op frpl_fprpl _ = () val op frpl_fprpl = TDB.find "frpl_fprpl"
  fun op ffv_frpl _ = () val op ffv_frpl = TDB.find "ffv_frpl"
  fun op frpl_id _ = () val op frpl_id = TDB.find "frpl_id"
  fun op ffv_frpl_SUBSET _ = ()
  val op ffv_frpl_SUBSET = TDB.find "ffv_frpl_SUBSET"
  fun op wff_IMP _ = () val op wff_IMP = TDB.find "wff_IMP"
  fun op wfvmap_IN_ofMAP_wfs _ = ()
  val op wfvmap_IN_ofMAP_wfs = TDB.find "wfvmap_IN_ofMAP_wfs"
  fun op ffv_finst_alt _ = ()
  val op ffv_finst_alt = TDB.find "ffv_finst_alt"
  fun op finst_o_vmap _ = () val op finst_o_vmap = TDB.find "finst_o_vmap"
  fun op FDOM_fVmap_fVrn _ = ()
  val op FDOM_fVmap_fVrn = TDB.find "FDOM_fVmap_fVrn"
  fun op FAPPLY_fVmap_fVrn _ = ()
  val op FAPPLY_fVmap_fVrn = TDB.find "FAPPLY_fVmap_fVrn"
  fun op uniqifn_FDOM_SUBSET _ = ()
  val op uniqifn_FDOM_SUBSET = TDB.find "uniqifn_FDOM_SUBSET"
  fun op fVinst_ffVrn _ = () val op fVinst_ffVrn = TDB.find "fVinst_ffVrn"
  fun op uniqifn_ex _ = () val op uniqifn_ex = TDB.find "uniqifn_ex"
  fun op FDOM_rn2fVmap _ = ()
  val op FDOM_rn2fVmap = TDB.find "FDOM_rn2fVmap"
  fun op FAPPLY_rn2fVmap _ = ()
  val op FAPPLY_rn2fVmap = TDB.find "FAPPLY_rn2fVmap"
  fun op MAP_tprpl_mk_bmap_REVERSE _ = ()
  val op MAP_tprpl_mk_bmap_REVERSE = TDB.find "MAP_tprpl_mk_bmap_REVERSE"
  fun op ffVrn_fVinst _ = () val op ffVrn_fVinst = TDB.find "ffVrn_fVinst"
  fun op wfvmap_presname _ = ()
  val op wfvmap_presname = TDB.find "wfvmap_presname"
  fun op fVinst_FALLL _ = () val op fVinst_FALLL = TDB.find "fVinst_FALLL"
  fun op wffVmap_o_fVmap _ = ()
  val op wffVmap_o_fVmap = TDB.find "wffVmap_o_fVmap"
  fun op wffVmap_fVmap_fVrn _ = ()
  val op wffVmap_fVmap_fVrn = TDB.find "wffVmap_fVmap_fVrn"
  fun op finst_FALLL _ = () val op finst_FALLL = TDB.find "finst_FALLL"
  fun op IN_slfv' _ = () val op IN_slfv' = TDB.find "IN_slfv'"
  fun op wffVmap_vinst_fVmap _ = ()
  val op wffVmap_vinst_fVmap = TDB.find "wffVmap_vinst_fVmap"
  fun op ffv_ffVrn _ = () val op ffv_ffVrn = TDB.find "ffv_ffVrn"
  fun op ofFMAP_SUBSET_ffv_fVinst _ = ()
  val op ofFMAP_SUBSET_ffv_fVinst = TDB.find "ofFMAP_SUBSET_ffv_fVinst"
  fun op wffVmap_DRESTRICT _ = ()
  val op wffVmap_DRESTRICT = TDB.find "wffVmap_DRESTRICT"
  
  
val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "newdefs"

val newdefs_grammars = valOf (Parse.grammarDB {thyname = "newdefs"})
end
