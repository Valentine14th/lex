law "U.S. Code"

#span_unit d

title "26"

title[1] "A"

chapter "1"

chapter[1] "B"

section "III"

article "121"

type individual
type property

internal functional event amount_excluded_from_gross_income_by_property(p: property, i: individual) -> money USD

internal functional event amount_excluded_from_gross_income(i: individual) -> money USD

internal functional event time_in_principal_residence(i: individual, p: property) -> span

observable event uses_property_as_principal_residence
  i: individual
  p: property
  
observable event owns_property
  i: individual
  p: property
  
observable event gain_from_sale_or_exchange_of_property
  i: individual
  p: property
  g: money USD
  
observable event tax_day
  i: individual
    
paragraph "a"

note """
Gross income shall not include gain from the sale or exchange of property if, during the 5-year period ending on the date of the sale or exchange, such property has been owned and used by the taxpayer as the taxpayer’s principal residence for periods aggregating 2 years or more.
"""


rule "compute_time_in_principal_residence"
  whenever
    gain_from_sale_or_exchange_of_property(i, p, gain)
    { t = SUM (1d; i, p; ONCE[0, 5y] uses_property_as_principal_residence(i, p) AND owns_property(i, p)) }
  constitute
    { time_in_principal_residence(i, p) = t }
    
rule "compute_amount_excluded_from_gross_income_by_property"
  whenever
    gain_from_sale_or_exchange_of_property(i, p, gain)
    { time_in_principal_residence(i, p) >= 2y }
  constitute
    { amount_excluded_from_gross_income_by_property(p, i) = gain }
     
rule "compute_amount_excluded_from_gross_income"
  whenever
    tax_day(i)
    { a = SUM (amount_excluded_from_gross_income_by_property(p, i); p; ONCE[0, 1y) TRUE) }
  constitute
    { amount_excluded_from_gross_income(i) = a }
   
paragraph "b"

point "1"

note """
The amount of gain excluded from gross income under subsection (a) with respect to any sale or exchange shall not exceed $250,000.
"""

# can be rewritten with "modify"

rule "compute_amount_excluded_from_gross_income_by_property"
  whenever
    gain_from_sale_or_exchange_of_property(i, p, gain)
    { gain > USD 250000 }
    { time_in_principal_residence(i, p) >= 2y }
  constitute 
    { amount_excluded_from_gross_income_by_property(p, i) = USD 250000 }

rule "exception_paragraph_a"
  whenever
    gain_from_sale_or_exchange_of_property(i, p, gain)
    { gain > USD 250000 }
    { time_in_principal_residence(i, p) >= 2y }
  except
    { paragraph "a" }
   

