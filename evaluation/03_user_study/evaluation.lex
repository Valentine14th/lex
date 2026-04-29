law "GDPR"

article "7"

paragraph "1"

type entity
type data
type data_subject
type activity
type consent

event Process
  """Controller {c} processes data {d} as part of activity {a}"""
  c : entity
  a : activity
  d : data

predicate PersonalData
  """Data {d} is personal data of data subject {ds}"""
  d  : data
  ds : data_subject

predicate IsBasedOnConsent
  """Activity {a} is based on consent {co}"""
  a  : activity
  co : consent

event GiveConsent
  """Data subject {ds} gives consent {co}"""
  ds : data_subject
  co : consent

predicate IsAbleToDemonstrateConsent
  """Controller {c} is able to demonstrate that consent {co} has been given """
  c  : entity
  co : consent
  
rule
  """Where processing is based on consent, the controller shall be able to demonstrate that the data subject has consented to processing of his or her personal data."""
  whenever
    Process(c, a, d)
    PersonalData(d, ds)
    IsBasedOnConsent(a, co)
    GiveConsent(ds, co)
  oblige
    IsAbleToDemonstrateConsent(c, co)
