refine paper

type user_id    is string
type data_class is string
type data_field is string
type data_id    is string

observable event create
    cls     : data_class
    caller  : user_id
    owner   : user_id
    purpose : purpose

suppressable event read
    cls     : data_class
    field   : data_field
    id      : data_id
    caller  : user_id
    owner   : user_id
    purpose : purpose

suppressable event write
    cls     : data_class
    field   : data_field
    id      : data_id
    caller  : user_id
    value   : string
    owner   : user_id
    purpose : purpose

causable observable event delete
    cls     : data_class
    id      : data_id
    caller  : user_id
    owner   : user_id
    purpose : purpose

observable event execute
    cls     : data_class
    field   : data_field
    id      : data_id
    caller  : user_id
    owner   : user_id
    purpose : purpose

observable event input
    func    : string
    param   : string
    value   : string
    caller  : string
    purpose : string

suppressable event output
    func    : string
    param   : string
    value   : string
    caller  : string
    purpose : string

refine type data_subject is user_id
refine type entity       is string
refine type data         is data_id
refine type activity     is purpose
refine type interest     is string
refine type purpose      is string
refine type nonexistent  is int

rule "refine_data_processing"
    whenever
        read(cls, field, id, caller, owner, purpose) OR (EXISTS value. write(cls, field, id, caller, value, owner, purpose))
    refine
        DataProcessing("Minitwit", "Minitwit", purpose, id)

rule "refine_personal_data"
    whenever
        read(cls, field, id, caller, owner, purpose) OR (EXISTS value. write(cls, field, id, caller, value, owner, purpose))
    refine
        PersonalData(id, owner)

assume true IsFair
assume true IsTransparent

rule "refine_iscollect"
    whenever
        input(func, param, value, caller, purpose)
    refine
        IsCollection(purpose)

rule "refine_giveconsent"
    whenever
        input("SetCookieConsentView", "accept", "true", caller, "service")
    refine
        GiveConsent(caller, "marketing", "Minitwit")

rule "refine_isnecessaryforlegitimateinterest"
    whenever
        true
    refine
        IsNecessaryForLegitimateInterest("service", "Minitwit", "being able to provide the service")

assume false IsOverridenByDataSubjectInterests
assume false inexistentEvent

