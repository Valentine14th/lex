law "U.S. Code"

title "26"

title[1] "A"

chapter "1"

chapter[1] "B"

section "III"

article "121"

type individual
type property

# test
# TODO[JD] Parser error at example/tax code/tax.lex:20:87: invalid character
internal functional event amount_excluded_from_gross_income_by_property (p : property, i: individual) -> money USD
  """ the amount excluded from gross income of individual {i} due to sale or exchange of property {p} """

internal functional event amount_excluded_from_gross_income(i: individual) -> money USD
  """ the total amount excluded from gross income of individual {i} due to sale or exchange of properties """

internal functional event time_in_principal_residence(i: individual, p: property) -> span
  """ the amount of time that individual {i} used property {p} as their principal residence """

observable event uses_property_as_principal_residence
  """ individual {i} uses property {p} as their principal residence """
  i: individual
  p: property

observable event owns_property
  """ individual {i} owns property {p} """
  i: individual
  p: property

observable event gain_from_sale_or_exchange_of_property
  """ individual {i} gains {g} from sale or exchange of their property {p} """
  i: individual
  p: property
  g: money USD

observable event tax_day
  """ it is tax day for individual {i} """
  i: individual

paragraph "a"

note """
Gross income shall not include gain from the sale or exchange of property if, during the 5-year period ending on the date of the sale or exchange, such property has been owned and used by the taxpayer as the taxpayer’s principal residence for periods aggregating 2 years or more.
"""

rule "time_in_principal_residence"
  whenever
    gain_from_sale_or_exchange_of_property(i, p, gain)
    t <- CNT (d; i, p; ONCE[0, 5y] uses_property_as_principal_residence(i, p) \ 
                                   AND owns_property(i, p) \
	                           AND (ts = cur_time) \
	                           AND (day(cur_time) = d) )
  constitute
    time_in_principal_residence(i, p) = 1d * t

rule "amount_excluded_by_property"
  whenever
    gain_from_sale_or_exchange_of_property(i, p, gain)
    time_in_principal_residence(i, p) = t
    t >= 2y
  constitute
    amount_excluded_from_gross_income_by_property(p, i) = gain
  
rule "amount_excluded"
  whenever
    tax_day(i)
    a <- SUM (t; p, i; ONCE[0, 1y) amount_excluded_from_gross_income_by_property(p, i) = t)
  constitute
    amount_excluded_from_gross_income(i) = a
   
paragraph "b"

point "1"

note """
The amount of gain excluded from gross income under subsection (a) with respect to any sale or exchange shall not exceed $250,000.
"""

# maybe improve to support modify... constitute

rule
  whenever
    gain_from_sale_or_exchange_of_property(i, p, gain)
    gain > USD 250000
    time_in_principal_residence(i, p) = t
    t >= 2y
  replace
    paragraph "a" rule "amount_excluded_by_property" 
  constitute
    amount_excluded_from_gross_income_by_property(p, i) = USD 250000
