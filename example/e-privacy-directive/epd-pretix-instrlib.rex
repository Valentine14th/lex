refine rex epd

observable event write
    cls: string
    field: string
    id: int
    caller: string
    value: string
    owner: string
    purpose: string

suppressable event read
    cls: string
    field: string
    id: int
    caller: string
    owner: string
    purpose: string

observable event input
    func: string
    param: string
    value: string
    caller: string
    purpose: string

rule "refine give consent"
    whenever
        write("Order", "marketing_email_consent", id, caller, "True", email, purpose)
    refine
        userGivesConsent(r, "Pretix")

rule "refine withdraw consent"
    whenever
        write("Order", "marketing_email_consent", id, caller, "False", email, purpose)
    refine
        userWithdrawsConsent(r, "Pretix")

# rule "fix pretix as sender"
#     whenever
