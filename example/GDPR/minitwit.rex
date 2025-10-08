refine paper

type user_id   is string
type data_type is string
type data_id   is string

suppressable event Read
    id      : data_id
    owner   : user_id
    purpose : purpose

suppressable event Write
    id      : data_id
    owner   : user_id
    purpose : purpose

observable event Collect
    purpose : purpose

observable event AcceptDataUsage
    caller  : user_id

refine type data_subject is user_id
refine type entity       is string
refine type data         is data_id
refine type activity     is purpose
refine type interest     is string

rule "refine_data_processing"
    whenever
        Read(id, owner, purpose) OR Write(id, owner, purpose)
    refine
        DataProcessing("Minitwit", "Minitwit", purpose, id)

rule "refine_personal_data"
    whenever
        Read(id, owner, purpose) OR Write(id, owner, purpose)
    refine
        PersonalData(id, owner)

assume true IsFair
assume true IsTransparent

rule "refine_iscollect"
    whenever
        Collect(purpose)
    refine
        IsCollection(purpose)

rule "refine_giveconsent"
    whenever
        AcceptDataUsage(caller)
    refine
        GiveConsent(caller, "marketing", "Minitwit")

rule "refine_isnecessaryforlegitimateinterest"
    whenever
        true
    refine
        IsNecessaryForLegitimateInterest("service", "Minitwit", "being able to provide the service")

assume false IsOverridenByDataSubjectInterests

