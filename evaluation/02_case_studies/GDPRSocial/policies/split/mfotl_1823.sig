Collect(activity: string, data: string, owner: string, purpose: string)-
Contains(de: string, de2: string)+
ContestAccuracy(user: string, data: string, data': string)
Declaration(de: string)+
HasCategory(d: string, cat: string)
HasIntendedRecipient(d: string, e: string)
HasText(de: string, text: string)+
IsRecipientRequest(rq: string, d: string)
NoteCategory(cat: string)+
NoteCriteria(c: string)+
NoteDS(ds: string)+
NoteEntity(e: string)+
NotePurpose(p: string)+
NoteRequest(rq: string)+
NotifyRectification(entity: string, data: string, data': string)+
PersonalData(d: string, ds: string)
Read(id: string, owner: string, activity: string, purpose: string, user: string)-
RequestAccess(user: string, request: string)
RequestErasure(user: string, data: string, request: string)
RequestRectification(user: string, data: string, data': string, request: string)
RequestResponse(ds: string, rq: string, rs: string)+
Send(entity: string, data: string)
Write(id: string, owner: string, activity: string, purpose: string, user: string)-
fun string_of_category(cat: string) : string
fun string_of_criteria(c: string) : string
fun string_of_ds(ds: string) : string
fun string_of_entity(c: string) : string
fun string_of_request(c: string) : string
