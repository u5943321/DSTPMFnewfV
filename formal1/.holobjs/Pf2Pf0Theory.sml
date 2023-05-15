structure Pf2Pf0Theory :> Pf2Pf0Theory =
struct
  
  val _ = if !Globals.print_thy_loads
    then TextIO.print "Loading Pf2Pf0Theory ... "
    else ()
  
  open Type Term Thm
  local open Pf0DrvTheory in end;
  
  structure TDB = struct
    val thydata = 
      TheoryReader.load_thydata "Pf2Pf0"
        (holpathdb.subst_pathvars "/Users/yimingxu/Documents/GitHub/DSTPMFnewfV/formal1/Pf2Pf0Theory.dat")
    fun find s = HOLdict.find (thydata,s)
  end
  
  fun op mp_match _ = () val op mp_match = TDB.find "mp_match"
  fun op agrees_on_def _ = ()
  val op agrees_on_def = TDB.find "agrees_on_def"
  fun op dest_imp_def _ = () val op dest_imp_def = TDB.find "dest_imp_def"
  fun op is_imp_def_primitive _ = ()
  val op is_imp_def_primitive = TDB.find "is_imp_def_primitive"
  fun op exFfmap_def _ = () val op exFfmap_def = TDB.find "exFfmap_def"
  fun op ax2th_def _ = () val op ax2th_def = TDB.find "ax2th_def"
  fun op uniqify_def _ = () val op uniqify_def = TDB.find "uniqify_def"
  fun op idfVmap_def _ = () val op idfVmap_def = TDB.find "idfVmap_def"
  fun op fVeff_def _ = () val op fVeff_def = TDB.find "fVeff_def"
  fun op UCI_def _ = () val op UCI_def = TDB.find "UCI_def"
  fun op UCIth_def _ = () val op UCIth_def = TDB.find "UCIth_def"
  fun op fVinsth_spec _ = () val op fVinsth_spec = TDB.find "fVinsth_spec"
  fun op fVinst_frpl _ = () val op fVinst_frpl = TDB.find "fVinst_frpl"
  fun op vinsth_spec _ = () val op vinsth_spec = TDB.find "vinsth_spec"
  fun op wff_FALL_no_vbound _ = ()
  val op wff_FALL_no_vbound = TDB.find "wff_FALL_no_vbound"
  fun op tfv_tinst_vinst_cont _ = ()
  val op tfv_tinst_vinst_cont = TDB.find "tfv_tinst_vinst_cont"
  fun op finst_frpl _ = () val op finst_frpl = TDB.find "finst_frpl"
  fun op uniqify_spec _ = () val op uniqify_spec = TDB.find "uniqify_spec"
  fun op ffVrn_frpl _ = () val op ffVrn_frpl = TDB.find "ffVrn_frpl"
  fun op wff_finst1 _ = () val op wff_finst1 = TDB.find "wff_finst1"
  fun op inst_eff_finst _ = ()
  val op inst_eff_finst = TDB.find "inst_eff_finst"
  fun op main_mp_case _ = () val op main_mp_case = TDB.find "main_mp_case"
  fun op wffV_fVrn _ = () val op wffV_fVrn = TDB.find "wffV_fVrn"
  fun op wffV_sinst_wffV _ = ()
  val op wffV_sinst_wffV = TDB.find "wffV_sinst_wffV"
  fun op uniqifn_DISJOINT_IMAGE_DISJOINT _ = ()
  val op uniqifn_DISJOINT_IMAGE_DISJOINT = TDB.find
    "uniqifn_DISJOINT_IMAGE_DISJOINT"
  fun op wfcfVmap_inst_EX _ = ()
  val op wfcfVmap_inst_EX = TDB.find "wfcfVmap_inst_EX"
  fun op wff_wfvl_mk_FALLL _ = ()
  val op wff_wfvl_mk_FALLL = TDB.find "wff_wfvl_mk_FALLL"
  fun op SUBMAP_agrees_on _ = ()
  val op SUBMAP_agrees_on = TDB.find "SUBMAP_agrees_on"
  fun op insth_unqify_MP0 _ = ()
  val op insth_unqify_MP0 = TDB.find "insth_unqify_MP0"
  fun op ofFMAP_EMPTY_iff _ = ()
  val op ofFMAP_EMPTY_iff = TDB.find "ofFMAP_EMPTY_iff"
  fun op uniqify_concl_is_imp _ = ()
  val op uniqify_concl_is_imp = TDB.find "uniqify_concl_is_imp"
  fun op insth_concl_is_imp _ = ()
  val op insth_concl_is_imp = TDB.find "insth_concl_is_imp"
  fun op insth_uniqify_mp _ = ()
  val op insth_uniqify_mp = TDB.find "insth_uniqify_mp"
  fun op Pf0Drv_mp_match_MP0 _ = ()
  val op Pf0Drv_mp_match_MP0 = TDB.find "Pf0Drv_mp_match_MP0"
  fun op insth_uniqify_mp_match _ = ()
  val op insth_uniqify_mp_match = TDB.find "insth_uniqify_mp_match"
  fun op fVinsth_mp_match _ = ()
  val op fVinsth_mp_match = TDB.find "fVinsth_mp_match"
  fun op vinsth_mp_match _ = ()
  val op vinsth_mp_match = TDB.find "vinsth_mp_match"
  fun op uniqify_mp_match _ = ()
  val op uniqify_mp_match = TDB.find "uniqify_mp_match"
  fun op fVinsth_cong _ = () val op fVinsth_cong = TDB.find "fVinsth_cong"
  fun op vinsth_cong _ = () val op vinsth_cong = TDB.find "vinsth_cong"
  fun op uniqify_cong _ = () val op uniqify_cong = TDB.find "uniqify_cong"
  fun op agrees_on_fVinst _ = ()
  val op agrees_on_fVinst = TDB.find "agrees_on_fVinst"
  fun op agrees_on_finst _ = ()
  val op agrees_on_finst = TDB.find "agrees_on_finst"
  fun op agrees_on_ffVrn _ = ()
  val op agrees_on_ffVrn = TDB.find "agrees_on_ffVrn"
  fun op agrees_on_SUBSET _ = ()
  val op agrees_on_SUBSET = TDB.find "agrees_on_SUBSET"
  fun op agrees_on_ofFMAP _ = ()
  val op agrees_on_ofFMAP = TDB.find "agrees_on_ofFMAP"
  fun op uniqifn_inst_EX _ = ()
  val op uniqifn_inst_EX = TDB.find "uniqifn_inst_EX"
  fun op ffVrn_is_imp _ = () val op ffVrn_is_imp = TDB.find "ffVrn_is_imp"
  fun op concl_insth_uniqify _ = ()
  val op concl_insth_uniqify = TDB.find "concl_insth_uniqify"
  fun op assum_insth_uniqify _ = ()
  val op assum_insth_uniqify = TDB.find "assum_insth_uniqify"
  fun op cont_insth_uniqify _ = ()
  val op cont_insth_uniqify = TDB.find "cont_insth_uniqify"
  fun op insth_uniqify_components _ = ()
  val op insth_uniqify_components = TDB.find "insth_uniqify_components"
  fun op thm_cong _ = () val op thm_cong = TDB.find "thm_cong"
  fun op sfv_sinst_SUBSET_vinst_cont _ = ()
  val op sfv_sinst_SUBSET_vinst_cont = TDB.find
    "sfv_sinst_SUBSET_vinst_cont"
  fun op wfvmap_FUPDATE _ = ()
  val op wfvmap_FUPDATE = TDB.find "wfvmap_FUPDATE"
  fun op cont_gen _ = () val op cont_gen = TDB.find "cont_gen"
  fun op insth_uniqify_gen _ = ()
  val op insth_uniqify_gen = TDB.find "insth_uniqify_gen"
  fun op NOTIN_Uof_lemma2 _ = ()
  val op NOTIN_Uof_lemma2 = TDB.find "NOTIN_Uof_lemma2"
  fun op Uof_sfv_SND_ofFMAP_SUBSET _ = ()
  val op Uof_sfv_SND_ofFMAP_SUBSET = TDB.find "Uof_sfv_SND_ofFMAP_SUBSET"
  fun op NOTIN_genavds_SUBSET_fVslfv _ = ()
  val op NOTIN_genavds_SUBSET_fVslfv = TDB.find
    "NOTIN_genavds_SUBSET_fVslfv"
  fun op Uof_slfv_SND_fVslfv _ = ()
  val op Uof_slfv_SND_fVslfv = TDB.find "Uof_slfv_SND_fVslfv"
  fun op DRESTRICT_FUPDATE_id _ = ()
  val op DRESTRICT_FUPDATE_id = TDB.find "DRESTRICT_FUPDATE_id"
  fun op fVslfv_finst _ = () val op fVslfv_finst = TDB.find "fVslfv_finst"
  fun op fVslfv_finst_ffVrn _ = ()
  val op fVslfv_finst_ffVrn = TDB.find "fVslfv_finst_ffVrn"
  fun op NOTIN_Uof_lemma _ = ()
  val op NOTIN_Uof_lemma = TDB.find "NOTIN_Uof_lemma"
  fun op assum_uniqify _ = ()
  val op assum_uniqify = TDB.find "assum_uniqify"
  fun op concl_uniqify _ = ()
  val op concl_uniqify = TDB.find "concl_uniqify"
  fun op NOTIN_genavds_assum_SUBSET_DELETE _ = ()
  val op NOTIN_genavds_assum_SUBSET_DELETE = TDB.find
    "NOTIN_genavds_assum_SUBSET_DELETE"
  fun op NOTIN_genavds_SUBSET_thfVars _ = ()
  val op NOTIN_genavds_SUBSET_thfVars = TDB.find
    "NOTIN_genavds_SUBSET_thfVars"
  fun op thfVars_SUBSET1 _ = ()
  val op thfVars_SUBSET1 = TDB.find "thfVars_SUBSET1"
  fun op thfVars_SUBSET _ = ()
  val op thfVars_SUBSET = TDB.find "thfVars_SUBSET"
  fun op Uof_fVslfv _ = () val op Uof_fVslfv = TDB.find "Uof_fVslfv"
  fun op Uof_slfv_SND_thfVars_uniqify _ = ()
  val op Uof_slfv_SND_thfVars_uniqify = TDB.find
    "Uof_slfv_SND_thfVars_uniqify"
  fun op IMAGE_vinst_fVar_thfVars_eq _ = ()
  val op IMAGE_vinst_fVar_thfVars_eq = TDB.find
    "IMAGE_vinst_fVar_thfVars_eq"
  fun op vinst_fVar_eq _ = ()
  val op vinst_fVar_eq = TDB.find "vinst_fVar_eq"
  fun op MEM_SUBSET_slfv _ = ()
  val op MEM_SUBSET_slfv = TDB.find "MEM_SUBSET_slfv"
  fun op ofFMAP_BIGUNION _ = ()
  val op ofFMAP_BIGUNION = TDB.find "ofFMAP_BIGUNION"
  fun op assum_vinsth _ = () val op assum_vinsth = TDB.find "assum_vinsth"
  fun op concl_vinsth _ = () val op concl_vinsth = TDB.find "concl_vinsth"
  fun op wfsigaxs_def1 _ = ()
  val op wfsigaxs_def1 = TDB.find "wfsigaxs_def1"
  fun op thfVars_gen _ = () val op thfVars_gen = TDB.find "thfVars_gen"
  fun op fVars_mk_FALL _ = ()
  val op fVars_mk_FALL = TDB.find "fVars_mk_FALL"
  fun op genavds_uniqify _ = ()
  val op genavds_uniqify = TDB.find "genavds_uniqify"
  fun op slfv_fVrn _ = () val op slfv_fVrn = TDB.find "slfv_fVrn"
  fun op slfv_SND_fVrn _ = ()
  val op slfv_SND_fVrn = TDB.find "slfv_SND_fVrn"
  fun op ffv_ffVrn1 _ = () val op ffv_ffVrn1 = TDB.find "ffv_ffVrn1"
  fun op fVinsth_gen _ = () val op fVinsth_gen = TDB.find "fVinsth_gen"
  fun op vinsth_gen1 _ = () val op vinsth_gen1 = TDB.find "vinsth_gen1"
  fun op vinsth_gen _ = () val op vinsth_gen = TDB.find "vinsth_gen"
  fun op uniqify_gen _ = () val op uniqify_gen = TDB.find "uniqify_gen"
  fun op finst_FUPDATE_as_frename _ = ()
  val op finst_FUPDATE_as_frename = TDB.find "finst_FUPDATE_as_frename"
  fun op tinst_FUPDATE_as_trename _ = ()
  val op tinst_FUPDATE_as_trename = TDB.find "tinst_FUPDATE_as_trename"
  fun op Pf0Drv_gen1 _ = () val op Pf0Drv_gen1 = TDB.find "Pf0Drv_gen1"
  fun op gen_precise_maps_ex1 _ = ()
  val op gen_precise_maps_ex1 = TDB.find "gen_precise_maps_ex1"
  fun op main_vinsth_case _ = ()
  val op main_vinsth_case = TDB.find "main_vinsth_case"
  fun op Pf2Pf0_vinst_lemma1 _ = ()
  val op Pf2Pf0_vinst_lemma1 = TDB.find "Pf2Pf0_vinst_lemma1"
  fun op wffV_wffVsl _ = () val op wffV_wffVsl = TDB.find "wffV_wffVsl"
  fun op Pf0Drv_MP0' _ = () val op Pf0Drv_MP0' = TDB.find "Pf0Drv_MP0'"
  fun op is_imp_def _ = () val op is_imp_def = TDB.find "is_imp_def"
  fun op is_imp_ind _ = () val op is_imp_ind = TDB.find "is_imp_ind"
  fun op Pf0Drv_MP0 _ = () val op Pf0Drv_MP0 = TDB.find "Pf0Drv_MP0"
  fun op MP0_def _ = () val op MP0_def = TDB.find "MP0_def"
  fun op MP0_ind _ = () val op MP0_ind = TDB.find "MP0_ind"
  fun op thfVars_assume _ = ()
  val op thfVars_assume = TDB.find "thfVars_assume"
  fun op ofFMAP_tfv_vinst_cont _ = ()
  val op ofFMAP_tfv_vinst_cont = TDB.find "ofFMAP_tfv_vinst_cont"
  fun op main_double_neg_lemma _ = ()
  val op main_double_neg_lemma = TDB.find "main_double_neg_lemma"
  fun op fVinst_NEG _ = () val op fVinst_NEG = TDB.find "fVinst_NEG"
  fun op finst_NEG _ = () val op finst_NEG = TDB.find "finst_NEG"
  fun op ffVrn_NEG _ = () val op ffVrn_NEG = TDB.find "ffVrn_NEG"
  fun op main_gen_case _ = ()
  val op main_gen_case = TDB.find "main_gen_case"
  fun op sfv_SUBSET_DELETE _ = ()
  val op sfv_SUBSET_DELETE = TDB.find "sfv_SUBSET_DELETE"
  fun op main_gen_case_ffv_fVinst_lemma1 _ = ()
  val op main_gen_case_ffv_fVinst_lemma1 = TDB.find
    "main_gen_case_ffv_fVinst_lemma1"
  fun op ofFMAP_SUBSET_FDOM _ = ()
  val op ofFMAP_SUBSET_FDOM = TDB.find "ofFMAP_SUBSET_FDOM"
  fun op ffv_plainfV _ = () val op ffv_plainfV = TDB.find "ffv_plainfV"
  fun op slfv_fVslfv _ = () val op slfv_fVslfv = TDB.find "slfv_fVslfv"
  fun op slfv_SUBSET_ffv _ = ()
  val op slfv_SUBSET_ffv = TDB.find "slfv_SUBSET_ffv"
  fun op uniqify_fVinst _ = ()
  val op uniqify_fVinst = TDB.find "uniqify_fVinst"
  fun op FDOM_idfVmap _ = () val op FDOM_idfVmap = TDB.find "FDOM_idfVmap"
  fun op FAPPLY_idfVmap _ = ()
  val op FAPPLY_idfVmap = TDB.find "FAPPLY_idfVmap"
  fun op fprpl_mk_bmap_REVERSE_plainfV _ = ()
  val op fprpl_mk_bmap_REVERSE_plainfV = TDB.find
    "fprpl_mk_bmap_REVERSE_plainfV"
  fun op fVeff_fVinst_cong _ = ()
  val op fVeff_fVinst_cong = TDB.find "fVeff_fVinst_cong"
  fun op FUNION_fVeff_cong _ = ()
  val op FUNION_fVeff_cong = TDB.find "FUNION_fVeff_cong"
  fun op ofFMAP_differ_2_SUBSET_lemma _ = ()
  val op ofFMAP_differ_2_SUBSET_lemma = TDB.find
    "ofFMAP_differ_2_SUBSET_lemma"
  fun op fVinsth_FUNION_fVeff _ = ()
  val op fVinsth_FUNION_fVeff = TDB.find "fVinsth_FUNION_fVeff"
  fun op wffVmap_FUNION _ = ()
  val op wffVmap_FUNION = TDB.find "wffVmap_FUNION"
  fun op wffV_wff_plainfV _ = ()
  val op wffV_wff_plainfV = TDB.find "wffV_wff_plainfV"
  fun op wffVmap_idfVmap _ = ()
  val op wffVmap_idfVmap = TDB.find "wffVmap_idfVmap"
  fun op PfDrv_fVinsth1 _ = ()
  val op PfDrv_fVinsth1 = TDB.find "PfDrv_fVinsth1"
  fun op PfDrv_thfVars_wffV0 _ = ()
  val op PfDrv_thfVars_wffV0 = TDB.find "PfDrv_thfVars_wffV0"
  fun op ffVrn_eq _ = () val op ffVrn_eq = TDB.find "ffVrn_eq"
  fun op uniqify_DRESTRICT _ = ()
  val op uniqify_DRESTRICT = TDB.find "uniqify_DRESTRICT"
  fun op PfDrv_uniqify _ = ()
  val op PfDrv_uniqify = TDB.find "PfDrv_uniqify"
  fun op insth_uniqify_fVinsth _ = ()
  val op insth_uniqify_fVinsth = TDB.find "insth_uniqify_fVinsth"
  fun op ofFMAP_Uof _ = () val op ofFMAP_Uof = TDB.find "ofFMAP_Uof"
  fun op Uof_fVars_finst_ffVrn _ = ()
  val op Uof_fVars_finst_ffVrn = TDB.find "Uof_fVars_finst_ffVrn"
  fun op fVinst_o_Vmap_finst_ffVrn _ = ()
  val op fVinst_o_Vmap_finst_ffVrn = TDB.find "fVinst_o_Vmap_finst_ffVrn"
  fun op vinst_cont_UNION _ = ()
  val op vinst_cont_UNION = TDB.find "vinst_cont_UNION"
  fun op ofFMAP_ffv_o_fVmap _ = ()
  val op ofFMAP_ffv_o_fVmap = TDB.find "ofFMAP_ffv_o_fVmap"
  fun op vinst_fVar_fVrn_eq_eq _ = ()
  val op vinst_fVar_fVrn_eq_eq = TDB.find "vinst_fVar_fVrn_eq_eq"
  fun op ffv_finst_ffVrn _ = ()
  val op ffv_finst_ffVrn = TDB.find "ffv_finst_ffVrn"
  fun op ofFMAP_fVars_SUBSET_fVars_fVinst _ = ()
  val op ofFMAP_fVars_SUBSET_fVars_fVinst = TDB.find
    "ofFMAP_fVars_SUBSET_fVars_fVinst"
  fun op fVinst_subset_lemma0 _ = ()
  val op fVinst_subset_lemma0 = TDB.find "fVinst_subset_lemma0"
  fun op ofFMAP_IMAGE _ = () val op ofFMAP_IMAGE = TDB.find "ofFMAP_IMAGE"
  fun op fVinst_subset_lemma _ = ()
  val op fVinst_subset_lemma = TDB.find "fVinst_subset_lemma"
  fun op cont_fVinsth _ = () val op cont_fVinsth = TDB.find "cont_fVinsth"
  fun op IMAGE_Uof _ = () val op IMAGE_Uof = TDB.find "IMAGE_Uof"
  fun op IMAGE_vinst_fVar_fVars _ = ()
  val op IMAGE_vinst_fVar_fVars = TDB.find "IMAGE_vinst_fVar_fVars"
  fun op thfVars_vinsth _ = ()
  val op thfVars_vinsth = TDB.find "thfVars_vinsth"
  fun op IMAGE_fVrn_fVars _ = ()
  val op IMAGE_fVrn_fVars = TDB.find "IMAGE_fVrn_fVars"
  fun op thfVars_uniqify _ = ()
  val op thfVars_uniqify = TDB.find "thfVars_uniqify"
  fun op is_cfm_fprpl _ = () val op is_cfm_fprpl = TDB.find "is_cfm_fprpl"
  fun op fVinst_cfVmap_is_cfm _ = ()
  val op fVinst_cfVmap_is_cfm = TDB.find "fVinst_cfVmap_is_cfm"
  fun op cfVmap_o_fVmap _ = ()
  val op cfVmap_o_fVmap = TDB.find "cfVmap_o_fVmap"
  fun op ofFMAP_DRESTRICT _ = ()
  val op ofFMAP_DRESTRICT = TDB.find "ofFMAP_DRESTRICT"
  fun op fVinsth_DRESTRICT _ = ()
  val op fVinsth_DRESTRICT = TDB.find "fVinsth_DRESTRICT"
  fun op uniqifn_DRESTRICT _ = ()
  val op uniqifn_DRESTRICT = TDB.find "uniqifn_DRESTRICT"
  fun op ffVrn_eq1 _ = () val op ffVrn_eq1 = TDB.find "ffVrn_eq1"
  fun op wfvmap_DRESTRICT _ = ()
  val op wfvmap_DRESTRICT = TDB.find "wfvmap_DRESTRICT"
  fun op vinst_cont_DRESTRICT _ = ()
  val op vinst_cont_DRESTRICT = TDB.find "vinst_cont_DRESTRICT"
  fun op vinsth_DRESTRICT _ = ()
  val op vinsth_DRESTRICT = TDB.find "vinsth_DRESTRICT"
  fun op vinsth_DRESTRICT1 _ = ()
  val op vinsth_DRESTRICT1 = TDB.find "vinsth_DRESTRICT1"
  fun op cont_uniqify _ = () val op cont_uniqify = TDB.find "cont_uniqify"
  fun op Uof_ffv_uniqify _ = ()
  val op Uof_ffv_uniqify = TDB.find "Uof_ffv_uniqify"
  fun op cfVmap_DRESTRICT _ = ()
  val op cfVmap_DRESTRICT = TDB.find "cfVmap_DRESTRICT"
  fun op wfcfVmap_DRESTRICT _ = ()
  val op wfcfVmap_DRESTRICT = TDB.find "wfcfVmap_DRESTRICT"
  fun op PfDrv_cont_is_cont _ = ()
  val op PfDrv_cont_is_cont = TDB.find "PfDrv_cont_is_cont"
  fun op precise_maps_ex _ = ()
  val op precise_maps_ex = TDB.find "precise_maps_ex"
  fun op Pf_assum_FINITE _ = ()
  val op Pf_assum_FINITE = TDB.find "Pf_assum_FINITE"
  fun op wffVmap_fVar_subfm_LENGTH _ = ()
  val op wffVmap_fVar_subfm_LENGTH = TDB.find "wffVmap_fVar_subfm_LENGTH"
  fun op thfVars_FAPPLY_IN_cont _ = ()
  val op thfVars_FAPPLY_IN_cont = TDB.find "thfVars_FAPPLY_IN_cont"
  fun op thfVars_slfv_cont_fVinsth _ = ()
  val op thfVars_slfv_cont_fVinsth = TDB.find "thfVars_slfv_cont_fVinsth"
  fun op fVars_FAPPLY_SUBSET_thfVars_fVinsth _ = ()
  val op fVars_FAPPLY_SUBSET_thfVars_fVinsth = TDB.find
    "fVars_FAPPLY_SUBSET_thfVars_fVinsth"
  fun op Pf0Drv_cont_SUBSET_cong _ = ()
  val op Pf0Drv_cont_SUBSET_cong = TDB.find "Pf0Drv_cont_SUBSET_cong"
  fun op Pf0Drv_cont_assum_SUBSET_cong _ = ()
  val op Pf0Drv_cont_assum_SUBSET_cong = TDB.find
    "Pf0Drv_cont_assum_SUBSET_cong"
  fun op ffv_ffVinst_SUBSET_cont_fVinsth _ = ()
  val op ffv_ffVinst_SUBSET_cont_fVinsth = TDB.find
    "ffv_ffVinst_SUBSET_cont_fVinsth"
  fun op wffVmap_ofFMAP_var_wf _ = ()
  val op wffVmap_ofFMAP_var_wf = TDB.find "wffVmap_ofFMAP_var_wf"
  fun op vinst_cont_wf _ = ()
  val op vinst_cont_wf = TDB.find "vinst_cont_wf"
  fun op ofFMAP_as_IMAGE _ = ()
  val op ofFMAP_as_IMAGE = TDB.find "ofFMAP_as_IMAGE"
  fun op ofFMAP_FINITE _ = ()
  val op ofFMAP_FINITE = TDB.find "ofFMAP_FINITE"
  fun op PfDrv_cont_FINITE _ = ()
  val op PfDrv_cont_FINITE = TDB.find "PfDrv_cont_FINITE"
  fun op ofFMAP_ffv_is_cont _ = ()
  val op ofFMAP_ffv_is_cont = TDB.find "ofFMAP_ffv_is_cont"
  fun op ofFMAP_tfv_is_cont _ = ()
  val op ofFMAP_tfv_is_cont = TDB.find "ofFMAP_tfv_is_cont"
  fun op vinst_cont_is_cont _ = ()
  val op vinst_cont_is_cont = TDB.find "vinst_cont_is_cont"
  fun op SUBSET_thfVars _ = ()
  val op SUBSET_thfVars = TDB.find "SUBSET_thfVars"
  fun op ffv_SUBSET_cont_fVinsth _ = ()
  val op ffv_SUBSET_cont_fVinsth = TDB.find "ffv_SUBSET_cont_fVinsth"
  fun op ffv_assum_SUBSET_cont_fVinsth _ = ()
  val op ffv_assum_SUBSET_cont_fVinsth = TDB.find
    "ffv_assum_SUBSET_cont_fVinsth"
  fun op cont_assum_concl _ = ()
  val op cont_assum_concl = TDB.find "cont_assum_concl"
  fun op uniqifn_INJ _ = () val op uniqifn_INJ = TDB.find "uniqifn_INJ"
  fun op main_fVinst_case _ = ()
  val op main_fVinst_case = TDB.find "main_fVinst_case"
  fun op Uof_concl_assum_SUBSET_cont _ = ()
  val op Uof_concl_assum_SUBSET_cont = TDB.find
    "Uof_concl_assum_SUBSET_cont"
  fun op gen_precise_maps_ex _ = ()
  val op gen_precise_maps_ex = TDB.find "gen_precise_maps_ex"
  fun op PfDrv_vinsth _ = () val op PfDrv_vinsth = TDB.find "PfDrv_vinsth"
  fun op vinsth_case_precise_maps_ex _ = ()
  val op vinsth_case_precise_maps_ex = TDB.find
    "vinsth_case_precise_maps_ex"
  fun op IN_cont_FAPPLY_SUBSET_cont_vinst _ = ()
  val op IN_cont_FAPPLY_SUBSET_cont_vinst = TDB.find
    "IN_cont_FAPPLY_SUBSET_cont_vinst"
  fun op wfcod_o_vmap _ = () val op wfcod_o_vmap = TDB.find "wfcod_o_vmap"
  fun op ofFMAP_fVars_rn2fVmap _ = ()
  val op ofFMAP_fVars_rn2fVmap = TDB.find "ofFMAP_fVars_rn2fVmap"
  fun op cont_vinsth _ = () val op cont_vinsth = TDB.find "cont_vinsth"
  fun op sfv_vinst_cont_SUBSET_MONO _ = ()
  val op sfv_vinst_cont_SUBSET_MONO = TDB.find "sfv_vinst_cont_SUBSET_MONO"
  fun op ffv_vinst_cont_SUBSET_MONO _ = ()
  val op ffv_vinst_cont_SUBSET_MONO = TDB.find "ffv_vinst_cont_SUBSET_MONO"
  fun op PfDrv_slfv_SUBSET_cont _ = ()
  val op PfDrv_slfv_SUBSET_cont = TDB.find "PfDrv_slfv_SUBSET_cont"
  fun op IMAGE_fVrn_fVrwinst_vinst_fVar _ = ()
  val op IMAGE_fVrn_fVrwinst_vinst_fVar = TDB.find
    "IMAGE_fVrn_fVrwinst_vinst_fVar"
  fun op ex_SUBSET_ofFMAP _ = ()
  val op ex_SUBSET_ofFMAP = TDB.find "ex_SUBSET_ofFMAP"
  fun op FAPPLY_o_fVmap1' _ = ()
  val op FAPPLY_o_fVmap1' = TDB.find "FAPPLY_o_fVmap1'"
  fun op FAPPLY_plainfV_bmap _ = ()
  val op FAPPLY_plainfV_bmap = TDB.find "FAPPLY_plainfV_bmap"
  fun op tprpl_fix _ = () val op tprpl_fix = TDB.find "tprpl_fix"
  fun op fprpl_fix _ = () val op fprpl_fix = TDB.find "fprpl_fix"
  fun op fVinst_plainfV _ = ()
  val op fVinst_plainfV = TDB.find "fVinst_plainfV"
  fun op fVrn_fVrwinst _ = ()
  val op fVrn_fVrwinst = TDB.find "fVrn_fVrwinst"
  fun op sinst_o_vmap _ = () val op sinst_o_vmap = TDB.find "sinst_o_vmap"
  fun op vinst_case_SUBSET_lemma _ = ()
  val op vinst_case_SUBSET_lemma = TDB.find "vinst_case_SUBSET_lemma"
  fun op ofFMAP_SUBSET_UNION_lemma _ = ()
  val op ofFMAP_SUBSET_UNION_lemma = TDB.find "ofFMAP_SUBSET_UNION_lemma"
  fun op ofFMAP_Uof_SUBSET_lemma2 _ = ()
  val op ofFMAP_Uof_SUBSET_lemma2 = TDB.find "ofFMAP_Uof_SUBSET_lemma2"
  fun op vinsth_case_SUBSET _ = ()
  val op vinsth_case_SUBSET = TDB.find "vinsth_case_SUBSET"
  fun op ffVrn_fabs _ = () val op ffVrn_fabs = TDB.find "ffVrn_fabs"
  fun op ffVrn_mk_FALL _ = ()
  val op ffVrn_mk_FALL = TDB.find "ffVrn_mk_FALL"
  fun op fVslfv_ffVrn _ = () val op fVslfv_ffVrn = TDB.find "fVslfv_ffVrn"
  fun op wff_ffVrn _ = () val op wff_ffVrn = TDB.find "wff_ffVrn"
  fun op ofFMAP_ffv_FINITE _ = ()
  val op ofFMAP_ffv_FINITE = TDB.find "ofFMAP_ffv_FINITE"
  fun op ofFMAP_tfv_FINITE _ = ()
  val op ofFMAP_tfv_FINITE = TDB.find "ofFMAP_tfv_FINITE"
  fun op vinst_cont_FINITE _ = ()
  val op vinst_cont_FINITE = TDB.find "vinst_cont_FINITE"
  fun op thfVars_add_cont1 _ = ()
  val op thfVars_add_cont1 = TDB.find "thfVars_add_cont1"
  fun op cont_add_cont1 _ = ()
  val op cont_add_cont1 = TDB.find "cont_add_cont1"
  fun op uniqify_refl _ = () val op uniqify_refl = TDB.find "uniqify_refl"
  fun op vinsth_refl _ = () val op vinsth_refl = TDB.find "vinsth_refl"
  fun op fVinsth_refl _ = () val op fVinsth_refl = TDB.find "fVinsth_refl"
  fun op thfVars_EQ _ = () val op thfVars_EQ = TDB.find "thfVars_EQ"
  fun op ffVrn_EQ _ = () val op ffVrn_EQ = TDB.find "ffVrn_EQ"
  fun op ffVrn_IFF _ = () val op ffVrn_IFF = TDB.find "ffVrn_IFF"
  fun op finst_IFF _ = () val op finst_IFF = TDB.find "finst_IFF"
  fun op fVinst_IFF _ = () val op fVinst_IFF = TDB.find "fVinst_IFF"
  fun op IFF_eq_eq _ = () val op IFF_eq_eq = TDB.find "IFF_eq_eq"
  fun op fVars_IFF _ = () val op fVars_IFF = TDB.find "fVars_IFF"
  fun op concl_fv_IN_thfVars_fVcong _ = ()
  val op concl_fv_IN_thfVars_fVcong = TDB.find "concl_fv_IN_thfVars_fVcong"
  fun op Rofeqthl_eqthl1 _ = ()
  val op Rofeqthl_eqthl1 = TDB.find "Rofeqthl_eqthl1"
  fun op Lofeqthl_eqthl1 _ = ()
  val op Lofeqthl_eqthl1 = TDB.find "Lofeqthl_eqthl1"
  fun op IMAGE_fVinst_finst_ffVrn_assum_eqthl _ = ()
  val op IMAGE_fVinst_finst_ffVrn_assum_eqthl = TDB.find
    "IMAGE_fVinst_finst_ffVrn_assum_eqthl"
  fun op eqths_cont_SUBSET_fVcong _ = ()
  val op eqths_cont_SUBSET_fVcong = TDB.find "eqths_cont_SUBSET_fVcong"
  fun op eqths_thfVars_SUBSET_fVcong _ = ()
  val op eqths_thfVars_SUBSET_fVcong = TDB.find
    "eqths_thfVars_SUBSET_fVcong"
  fun op main _ = () val op main = TDB.find "main"
  
  
val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "Pf2Pf0"

val Pf2Pf0_grammars = valOf (Parse.grammarDB {thyname = "Pf2Pf0"})
end
