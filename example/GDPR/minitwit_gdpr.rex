refine gdpr

type activity_id is string
type user_id     is string
type data_type   is string
type data_id     is string
type request_id  is string
type file_id     is string
type decl_id     is string

suppressable event Read
    id      : data_id
    owner   : user_id
    activity: activity_id
    purpose : purpose
    user    : user_id

suppressable event Write
    id      : data_id
    owner   : user_id
    activity: activity_id	
    purpose : purpose
    user    : user_id

observable event Collect
    activity: activity_id
    data    : data_id
    owner   : user_id
    purpose : purpose

observable event AcceptDataUsage
    caller  : user_id

causable observable event DailyErasureReview
    data    : data_id

suppressable event Consent
    user    : user_id
    purpose : purpose

suppressable event Revoke
    user    : user_id
    purpose : purpose

suppressable event SpecialConsent
    user    : user_id
    purpose : purpose
    sp      : special_data_category

observable event ContestAccuracy
    user    : user_id
    data    : data_id
    data'   : data_id

observable event RequestRectification
    user    : user_id
    data    : data_id
    data'   : data_id

observable event RequestAccess
    user    : user_id

causable observable event Declaration
    de      : decl_id

causable observable event HasText
    de      : decl_id
    text    : string

causable observable event NotifyErasure
    entity  : string
    data    : data_id

causable observable event NotifyRectification
    entity  : string
    data    : data_id
    data'   : data_id

causable observable event NotifyRestriction
    entity  : string
    data    : data_id
    purpose : purpose

observable event RequestObjection
    user    : user_id
    purpose : purpose
    de      : decl_id

causable observable event ActivityRecord
    activity: activity_id
    property: string
    value   : string

observable event Send
    entity  : string
    data    : data_id

causable observable event SendFile
    entity  : string
    file    : file_id

refine type activity     is activity_id
refine type data         is data_id
refine type data_subject is user_id
refine type entity       is string
refine type interest     is string
refine type declaration  is decl_id
refine type request      is request_id
refine type criteria     is string
refine type file         is file_id

note "### Events that are not taking place ###"

assume false AdequacyDecision
    """No transfers are taking place."""
    
assume false AssessTransfer
    """No transfers are taking place."""

assume false AuthorizeConsent
    """No delegation of consent in our model."""

assume false ChargeForRequest
    """We are never charging users for requests."""

assume false ConcernsCriminalRegister
    """We are never storing criminal register data."""

assume false DisproportionateEffortToInform
    """We never consider that it requires a disproportionate effort to inform third-parties."""

assume false EndContract
    """No contracts are being concluded."""

assume false FulfillsConsultationConditions
    """No transfers are taking place."""

assume false HasEnforceableRights
    """No transfers are taking place."""
    
assume false HasIntendedTransfer
    """No transfers are taking place."""

assume false HasPhilosophicalAim
    """No controller has a philosophical aim."""

assume false HasPoliticalAim
    """No controller has a political aim."""

assume false HasReligiousAim
    """No controller has a religious aim."""

assume false HasSupervisoryApproval
    """No transfers are taking place."""

assume false HasTradeUnionAim
    """No controller has a trade union aim."""

assume false ImplementFundamentalRightsSafeguards
    """We do not claim the impementation of fundamental rights safeguards for the processing of special data categories."""

assume false IsApprovedCertificationMechanism
    """No transfers are taking place."""

assume false IsApprovedCodeOfConduct
    """No transfers are taking place."""

assume false IsArchival
    """No archiving is performed."""

assume false IsBindingCorporateRules
    """No transfers are taking place."""

assume false IsCommissionStandardClauses
    """No transfers are taking place."""

assume true IsCommonlyUsedFormat
    """We only use structured file formats (JSON) for output."""

assume false IsContractParty
    """No contracts are being concluded."""

assume true IsElectronicDeclaration
    """All declarations are electronic."""
    
assume true IsElectronicRequest
    """All requests are electronic."""

assume false IsImpossibleElectronic
    """All requests are electronic."""

assume false IsInInterestOf
    """No contracts are being concluded."""

assume false IsJointController
    """There are no joint controllers."""

assume false IsLegallyBindingInstrument
    """No transfers are taking place."""

assume false IsLegitimateInterestRegister
    """No transfers are taking place."""

assume false IsLimitedDSTransfer
    """No transfers are taking place."""

assume false IsLimitedRegisterData
    """No transfers are taking place."""

assume true IsMachineReadableFormat
    """We only use structured file formats (JSON) for output."""

assume false IsMember
    """No membership in organizations is considered."""

assume false IsNecessaryForArchivalPurposes
    """No archiving is performed."""

assume false IsNecessaryForContract
    """No contracts are being concluded."""

assume false IsNecessaryForEmploymentLaw
    """We do not consider this legal basis."""

assume false IsNecessaryForFreedomOfExpression
    """We do not consider this legal basis."""

assume false IsNonProfit
    """No non-profit controller is involved."""

assume false IsNotRepetitiveTransfer
    """No transfers are taking place."""

assume false IsOccasionalProcessing
    """All processing is habitual, not occasional."""

assume false IsPublicAuthority
    """No public authority is involved."""

assume false IsOpenRegisterData
    """No open register is involved."""

assume true IsOutsideDisclosure
    """Data is generally disclosed to outsiders."""

assume false IsPerformanceOfPublicAuthorityTask
    """No public authority is involved."""

assume false IsReasonableFee
    """We generally do not impose fees."""

assume false IsReasonablePeriod
    """We do not wait to inform users."""

assume false IsReception
    """We do not receive data from other entities."""

assume false IsRisksOfTransfer
    """No transfers are taking place."""

assume false IsRiskyProcessing
    """None of the activities performed is likely to result to a high risk to the rights and freedoms of individual persons."""

assume false IsSpecialAuthorizedCriminalProcessing
    """We do not process criminal data."""

assume true IsStructuredFormat
    """We only use structured file formats (JSON) for output."""

assume false IsSubjectToProfessionalSecrecy
    """No entity is subject to the obligation of professional secrecy."""

assume false IsSupervisoryAuthorityStandardClauses
    """No transfers are taking place."""

assume false IsUnfoundedOrExcessive
    """We never qualify user requests as unfounded or excessive."""

assume false JustifiesStorage
    """No archiving is performed."""

assume false MakePublic
    """We never assume that a data subject makes their data public."""

assume false PrepareContract
    """No contracts are being concluded."""

assume false RefuseRequest
    """We never refuse requests."""

assume false RequestContractPreparation
    """No contracts are being concluded."""

assume false RequestExtension
    """We never request an extension."""

assume false RequestsNonElectronic
    """All requests are electronic."""

assume false StartContract
    """No contracts are being concluded."""

assume false Transfer
    """No transfers are taking place."""

assume false UndueDataDelay
    """We do not wait to delete data."""

assume false UndueDelay
    """We do not wait to inform users."""

assume false ValidRegisterConsultationRequest
    """No transfers are taking place."""

assume true DataIsNecessaryForJudicialClaims
    """We always take claims citing judicial reasons at face value."""

assume false DemonstrateOverridingCompellingGrounds
    """We never claim compelling groups that override the interests, rights, and freedoms of the data subject."""

assume false HasDataSubjectCategory
    """No activities are specific to a particular data subject category."""

assume false HasIntendedRecipientCategory
    """We have no intended recipient categories -- recipients are specified individually."""

assume false HasStatutoryContractualRequirement
    """No contracts are being concluded."""

assume false HasStoragePeriod
    """No storage period is defined. Data is kept until users delete their account."""

assume false HoldParentalResponsibility
    """Minors are not allowed to register to the service."""

assume false IsChild
    """Minors are not allowed to register to the service."""

assume true IsClearAndPlainLanguage
    """The text of all declarations is contained in this refinement file. They use clear and plain language."""

assume true IsConcise
    """The text of all declarations is contained in this refinement file. They are concise."""

assume true IsTransparentDeclaration
    """The text of all declarations is contained in this refinement file. They are transparent."""

assume false IsControllerRepresentative
    """We do not need controller representatives since all controllers considered are based in the Union."""

assume true IsDistinguishableFromOtherMatters
    """The text of all declarations is contained in this refinement file. They are independent and clearly distinguishable from other."""

assume true IsEasilyAccessible
    """The text of all declarations is contained in this refinement file. They are easily accessible."""

assume true IsIntelligible
    """The text of all declarations is contained in this refinement file. They are intelligible."""

assume true IsExplicit
    """The purposes (service, statistics, personalized_ad) are explicitly listed in the declaration at collection."""

assume false IsExtensionNecessary
    """We never claim that we need a time extension to process user requests."""

assume false IsLegitimateActivity
    """We never claim a legitimate activity with respect to a controller with a political, philosophical, religious, or trade union aim."""

assume true IsOfferOfInformationSocietyServices
    """Minitwit, Inc. provides information society services."""

assume true IsReasonForRequestExtension
    """Irrelevant since we never extend requests."""
    
assume true IsReasonForRequestRefusal
    """Irrelevant since we never refuse requests."""

assume true IsReceptionSource
    """Irrelevant since we never receive data from other sources."""

assume true IsRespected
    """The storage criteria are respected as users' data is deleted when their accounts are."""

assume true IsRisksOfTransfer
    """Irrelevant since no transfers are taking place."""

assume true IsSpecified
    """The purposes (service, statistics, personalized_ad) are specified in the declaration at collection."""

assume true IsTransfer
    """Irrelevant since no transfers are taking place."""

assume true IsTransferBasis
    """Irrelevant since no transfers are taking place."""
    
assume true IsUnableToConsent
    """When creating an account, users must self-certify that they are physically and legally able to consent."""

assume true ReportLastResortTransfer
    """Irrelevant since no transfers are taking place."""

assume false Stored
    """Irrelevant since IsNecessary is true."""

assume false TechnicalAndOrganisationalMeasures
    """We do not claim any technical and organizational measures for archival purposes."""

assume false UseForCommunication
    """Irrelevant since we never delay informing users."""

assume false ConsentDeclarationContainsOtherMatters
    """Consent declarations never contain other matters."""

assume true IsNewPurpose
    """Irrelevant since Article 13(3) is replaced by rule no_new_purpose."""

assume false IsStorage
    """We never assume that an activity is only a storage activity."""

note "### Other assumptions ###"

assume true IsFair
    """TODO: Complete informal justification of fairness"""

assume true IsTransparent
    """The automated enforcement of the GDPR requirement, in particular the ROPA logging mechanism, ensures transparency with respect to the user."""

assume true EnsuresAppropriateSecurity
    """TODO: Complete informal justification of security"""

assume true IsAdequate
    """TODO: Complete informal justification of data adequacy wrt purposes"""

assume true IsLimitedToWhatIsNecessary
    """TODO: Complete informal justification of limitation"""

assume true IsNecessary
    """TODO: Complete informal justification of necessity"""

assume true IsRelevant
    """TODO: Complete informal justification of data adequacy wrt purposes"""

assume true IsUpToDate
    """TODO: Complete informal justification of data being up to date"""

# TODO: IsCompatibleWithPurpose

note "### Refinement to system events ###"

rule "r_AutomatedDecision"
    """The only form of automated decision-making / profiling taking place concerns the selection of personalized ads. Otherwise, no profiling occurs."""
    whenever
        Read(d, ds, a, "personalized_ad", ds') OR Write(d, ds, a, "personalized_ad", ds')
    refine
        AutomatedDecision(a, d, ds', "We use the content of the page shown to the user to display personalized advertisement")

rule "r_CheckNotChild"
    """Users must upload a copy of their ID when registering, which is then semi-automatically vetted. Users below the age of 16 are not allowed to register. Hence, any user in hte system is at least 16. This fulfills our due diligence obligation."""
    whenever
        true
    refine
        CheckNotChild("Minitwit, Inc.", ds)

rule "r_ContestsAccuracy"
    whenever
        ContestAccuracy(ds, d, d')
    refine
        Request(ds, "", "Minitwit, Inc.")
        ContestsAccuracy("", d, d')

rule "r_DataProcessing"
    whenever
        Read(d, ds, a, p, ds') OR Write(d, ds, a, p, ds')
    refine
        DataProcessing("Minitwit, Inc.", "Minitwit, Inc.", a, d)

rule "r_DataReview"
    whenever
        DailyErasureReview(d)
    refine
        DataReview("Minitwit, Inc.", d)

rule "r_Disclose"
    whenever
        Read(d, ds, a, p, ds')
    refine
        Disclose(d, ds')

rule "r_GiveConsent"
    whenever
        Consent(ds, p) OR (EXISTS sp. SpecialConsent(ds, p, sp))
    refine
        GiveConsent(ds, p, "Minitwit, Inc.")

rule "r_GiveSpecialConsent"
    whenever
        SpecialConsent(ds, p, sp)
    refine
        GiveSpecialConsent(ds, p, "Minitwit, Inc.", sp)

rule "r_IsRectificationRequest"
    whenever
        RequestRectification(ds, d, d')
    refine
        Request(ds, "", "Minitwit, Inc.")
        IsRectificationRequest("", d, d')
        HasInaccuracy(d)

rule "r_HasIntendedAutomatedDecision"
    whenever
        Collect(a, d, ds, "personalized_ad")
    refine
        HasIntendedAutomatedDecision(d, "We use the content of the page shown to the user to display personalized advertisement")

rule "r_HasIntendedRecipient"
    whenever
        Collect(a, d, ds, "statistics")
    refine
        HasIntendedRecipientCategory(d, "Analytics, Inc.")

rule "r_HasPurpose"
    whenever
        Read(d, ds, a, p, ds') OR Write(d, ds, a, p, ds')
    refine
        HasPurpose(a, p)

rule "r_HasRegularContact"
    whenever
        true
    refine
        HasRegularContact(d, "Minitwit, Inc.")

rule "r_HasSecurityMeasuresDeclaration"
    whenever
        true
    refine
        HasSecurityMeasuresDeclaration(a, "TODO: Complete list of security measures")
	
rule "r_HasStorageCriteria"
    whenever
        true
    refine
        HasStorageCriteria(d, "Data is stored until the user deletes their account")

rule "r_IsAbleToDemonstrateConsent"
    """The presence of the Consent event in the trace demonstrates consent."""
    whenever
        ONCE Consent(ds, p)
    refine
        IsAbleToDemonstrateConsent("Minitwit, Inc.", ds, p)

rule "r_IsAccessRequest"
    whenever
        RequestAccess(ds)
    refine
        Request(ds, "", "Minitwit, Inc.")
        IsAccessRequest("")

rule "r_IsAccurate"
    """Data is assumed to be accurate unless their owner has contested its accuracy."""
    whenever
        NOT EXISTS d'. ONCE RequestRectification(ds, d, d')
    refine
        IsAccurate(d, p)

rule "r_IsAutomatedDecision"
    whenever
        Declaration(d)
        HasText(d, "We use the content of the page shown to the user to display personalized advertisement")
    refine
        IsAutomatedDecision(d)

rule "r_IsAutomatedDecisionMakingPurpose"
    whenever
        true
    refine
        IsAutomatedDecisionMakingPurpose("personalized_ad")

rule "r_IsCategory"
    whenever
        Declaration(d)
        HasText(d, "Some of the collected data belongs to the following special category: " + string_of_category(cat))
    refine
        IsCategory(d, cat)

rule "r_IsCollection"
    whenever
        Collect(a, d, ds, p)
    refine
        IsCollection(a, ds)

function string_of_request(
    c : request
) -> string

rule "r_IsComplaintStatement"
    whenever
        Declaration(d)
        HasText(d, "You have a right to lodge a complaint with the National DPA regarding request " + string_of_request(rq))
    refine
        IsComplaintStatement(d, rq)

rule "r_IsContactDetailsOfDataProtectionOfficer"
    whenever
        Declaration(d)
        HasText(d, "You can contact our data protection officer at: " + string_of_entity(c))
    refine
        IsContactDetailsOfDataProtectionOfficer(d, c)

function string_of_ds(
    ds : data_subject
) -> string

rule "r_IsDSSource"
    whenever
        Declaration(d)
        HasText(d, "We have collected this data from " + string_of_ds(ds))
    refine
        IsDSSource(d, ds)

rule "r_IsDataProcessingNotOngoing"
    whenever
        Declaration(d)
        HasText(d, "We are not currently processing your data.")
    refine
        IsDataProcessingNotOngoing(d)
	
rule "r_IsDataProcessingOngoing"
    whenever
        Declaration(d)
        HasText(d, "We are currently processing your data.")
    refine
        IsDataProcessingOngoing(d)

rule "r_IsDataProcessingOfficer"
    whenever
        c = "Minitwit, Inc."
        c' = "dpo@minitwit-inc.com"
    refine
        IsDataProtectionOfficer(c, c')

rule "r_IsDirectMarketing"
    whenever
        p = "personalized_ad"
    refine
        IsDirectMarketing(p)

rule "r_IsDirectTransmissionFeasible"
    whenever
        true
    refine
        IsDirectTransmissionFeasible("Minitwit, Inc.", "Othertwit, Inc.")

rule "r_IsIdentityOfControllerOrRepresentative"
    whenever
        Declaration(d)
        HasText(d, "The controller is " + string_of_entity(c))
    refine
        IsIdentityOfControllerOrRepresentative(d, c)

function string_of_legal_basis(
    b : legal_basis
) -> string

rule "r_IsLegalBasisOfProcessing"
    whenever
        Declaration(d)
        HasText(d, "The legal basis of the processing is Article " + string_of_legal_basis(b) + " GDPR")
    refine
        IsLegalBasisOfProcessing(d, b)

rule "r_IsLegitimate"
    whenever
        p = "service" OR p = "personalized_ad" OR p = "statistics"
    refine
        IsLegitimate(p)

function string_of_interest(
    i : interest
) -> string

rule "r_IsLegitimateInterest"
    whenever
        Declaration(d)
        HasText(d, "Entity " + string_of_entity(e) + " claims the following legitimate interest: " + string_of_interest(i))
    refine
        IsLegitimateInterest(d, e, i)
	
rule "r_IsNecessaryForLegitimateInterest"
    whenever
        Read(d, ds, a, p, ds') OR Write(d, ds, a, p, ds')
        p = "service"
    refine
        IsNecessaryForLegitimateInterest(a, "Minitwit, Inc.", "Providing the service and performing Minitwit's normal operations.")

rule "no_new_purpose"
    whenever
        EXISTS pr. DataProcessing(pr, c, a, d)
        PersonalData(d, ds)
        HasPurpose(a, p)
    oblige
        NOT ONCE (EXISTS co, pr'. DataProcessing(pr', c, co, d) AND IsCollection(co, ds) AND NOT HasPurpose(co, p))
    transparently enforceable suppressing condition[0]

replace
    strengthen
        article "13" paragraph "3"
    by
        rule "no_new_purpose"

rule "r_IsOverriddenByDataSubjectInterests"
    whenever
        Read(d, ds, a, p, ds') OR Write(d, ds, a, p, ds')
        NOT (p = "service")
    refine
        IsOverriddenByDataSubjectInterests(c, i, ds)

rule "r_IsPurposeOfProcessing"
    whenever
        Declaration(d)
        p = "service" IMPLIES HasText(d, "The purpose of processing is: providing Minitwit's essential functionality ('service').")
        p = "personalized_ad" IMPLIES HasText(d, "The purpose of processing is: personalized advertisement ('personalize_ad').")
        p = "statistics" IMPLIES HasText(d, "The purpose of processing is: website statistics and analytics ('statistics')")
    refine
        IsPurposeOfProcessing(d, p)

rule "r_IsRecipient"
    whenever
        Declaration(d)
        HasText(d, "We intend to share your data with the following entity: " + string_of_entity(e))
    refine
        IsRecipient(d, e)

rule "r_IsRecipientCategory"
    whenever
        Declaration(d)
        HasText(d, "We intend to share your data with the following categories of entities:  " + string_of_entity(e))
    refine
        IsRecipientCategory(d, e)

function string_of_data(
    d : data_id
) -> string

rule "r_IsRestrictionToBeLifted"
    whenever
        Declaration(d)
        HasText(d, "The restriction on data " + string_of_data(data) + " due to request " + string_of_request(rq) + " is to be lifted.")
    refine
        IsRestrictionToBeLifted(d, data, rq)

rule "r_IsRightToLodgeComplaint"
    whenever
        Declaration(d)
        HasText(d, "You have a right to lodge a complaint with the National DPA")
    refine
        IsRightToLodgeComplaint(d)

rule "r_IsRightToWithdrawConsent"
    whenever
        Declaration(d)
        HasText(d, "You have the right to withdraw consent at any time")
    refine
        IsRightToWithdrawConsent(d)

rule "r_IsRights"
    whenever
        Declaration(d)
        HasText(d, "You have the right to request from the controller to access, rectify, erase, or restrict the processing of any personal data we hold. You have the right to obtain a copy of your data in a machine-readable format to be easily ported to a different provider. You have the right to object to automated decision-making, including profiling.")
    refine
        IsRights(d)

rule "r_IsSME"
    whenever
        true
    refine
        IsSME("Minitwit, Inc.")

function string_of_criteria(
    c : criteria
) -> string

rule "r_IsStorageCriteria"
    whenever
        Declaration(d)
        HasText(d, "The condition under which we keep your data is: " + string_of_criteria(c))
    refine
        IsStorageCriteria(d, c)

rule "r_IsStoragePeriod"
    whenever
        Declaration(d)
        HasText(d, "The period for which we keep your data is: " + string_of_criteria(c))
    refine
        IsStorageCriteria(d, c)

# TODO: Discuss _
rule "r_NotifyOfErasure"
    whenever
        NotifyErasure(e, d)
    refine
        NotifyOfErasure(_, e, d)

rule "r_NotifyOfRectification"
    whenever
        NotifyRectification(e, d, d')
    refine
        NotifyOfRectification(_, e, d, d')

rule "r_NotifyOfRestriction"
    whenever
        NotifyRestriction(e, d, p)
    refine
        NotifyOfRestriction(_, e, d, p)

rule "r_Object"
    whenever
        RequestObjection(ds, p, de)
    refine
        Object(ds, "Minitwit, Inc.", p, de)

rule "r_Record"
    whenever
        ActivityRecord(a, p, v)
    refine
        Record(_, _, a, p, v)

rule "r_Share"
    whenever
        Send(e, d)
    refine
        Share("Minitwit, Inc.", e, d)

rule "r_Tranmit"
    whenever
        SendFile(e, f)
    refine
        Transmit(_, e, f)

rule "r_WithdrawConsent"
    whenever
        Revoke(ds, p)
    refine
        WithdrawConsent(ds, p, "Minitwit, Inc.")

note "### Not refined ###"
	        
# Contains
# ContainsData
# Delete
# HasCategory
# Inform
# IsCategory
# IsConsentRequest
# IsErasureRequest
# IsFurtherCopy
# IsNecessaryForPublicInterest
# IsHealthRelated
# IsNecessaryForImportantPublicInterest
# IsNecessaryForJudicialClaims
# IsNecessaryForLegalObligation
# IsNecessaryForProtectionOfRights
# IsNecessaryForSpecialMedicalReasons
# IsNecessaryForSubstantialPublicInterest
# IsNecessaryForVitalInterests
# IsPortabilityRequest
# IsRecipientRequest
# IsRectificationRequest
# IsRestrictionRequest
# IsSpecialData
# LiftRestriction
# RelatesToCriminalConvictionsOrOffences
# SpecifiesNewController
# PersonalData
# PersonalDataCopy
# Rectify
# RequestResponse
# Stored
# TP

note "END."