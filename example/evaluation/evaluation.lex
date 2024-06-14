law "GDPR"

article "7"

paragraph "1"

type entity   is string
type person   is string
type task     is int
type action   is int
type data     is int
type consent  is int

event Nominates
  """ Controller {c} nominates processor {p} to perform data processing task {t} """
  c: entity
  p: entity
  t: task

suppressable event Processes
  """ Processor {p} processes data {d} as part of data processing task {t}; this constitutes data processing action {pr} """
  pr: action
  p:  entity
  d:  data
  t:  task

predicate Relates
  """ Personal data {d} relates to data subject {ds} """
  d:  data
  ds: person

event LegalBasis
  """ Data processing action {pr} is based on consent {co} """
  pr: action
  co: consent

event GivesConsent
  """ Data subject {ds} gives consent {co} """
  ds: person
  co:  consent

event AbleToDemonstrateConsent
  """ Controller {c} is able to demonstrate that consent {co} has been given """
  c:  entity
  co: consent
  
rule
  """Where processing is based on consent, the controller shall be able to demonstrate that the data subject has consented to processing of his or her personal data."""
  whenever
    Nominates(c, p, t)
    Processes(pa, p, d, t)
    Relates(d, ds)
    LegalBasis(pa, co)
    GivesConsent(ds, co)
  oblige
    AbleToDemonstrateConsent(c, co)
transparently enforceable
suppressing Processes
