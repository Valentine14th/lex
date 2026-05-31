Collect(activity: string, data: string, owner: string, purpose: string)-
Consent(user: string, purpose: string)-
Contains(de: string, de2: string)+
ContestAccuracy(user: string, data: string, data': string)
Declaration(de: string)+
HasText(de: string, text: string)+
Inform(c: string, ds: string, de: string)+
IsHealthRelated(pi: string)
IsNecessaryForImportantPublicInterest(a: string, pi: string)
IsNecessaryForJudicialClaims(a: string)
IsNecessaryForLegalObligation(a: string, l: string)
IsNecessaryForProtectionOfRights(a: string, e: string)
IsNecessaryForPublicInterest(a: string, pi: string)
IsNecessaryForSpecialMedicalReasons(a: string)
IsNecessaryForSubstantialPublicInterest(a: string)
IsNecessaryForVitalInterests(a: string, ds': string, v: string)
IsRestrictionRequest(rq: string, d: string, p: string)
IsSpecialData(d: string, sp: string)
LiftRestriction(c: string, d: string, rq: string)-
NoteData(d: string)+
NoteEntity(e: string)+
NoteInterest(i: string)+
NoteRequest(rq: string)+
PersonalData(d: string, ds: string)
Read(id: string, owner: string, activity: string, purpose: string, user: string)-
Rectify(d_old: string, d_new: string)+
RelatesToCriminalConvictionsOrOffences(d: string)
RequestAccess(user: string, request: string)
RequestErasure(user: string, data: string, request: string)
RequestObjection(user: string, purpose: string, de: string, request: string)
RequestRectification(user: string, data: string, data': string, request: string)
RequestResponse(ds: string, rq: string, rs: string)+
Revoke(user: string, purpose: string)-
SpecialConsent(user: string, purpose: string, sp: string)-
Write(id: string, owner: string, activity: string, purpose: string, user: string)-
fun string_of_data(d: string) : string
fun string_of_entity(c: string) : string
fun string_of_interest(i: string) : string
fun string_of_request(c: string) : string
