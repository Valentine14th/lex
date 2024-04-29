import akomaNtoso BGG

law "BGG"
chapter "3"

type recht is string
type gericht is string
type gebiet is string
type gegenstand is string
type beschwerde is int
type akt is int
type person is string
type staat is string

predicate anfechtungsObjekt
  """ Beschwerde {b} fechtet Akt {a} an """
  b: beschwerde
  a: akt

predicate trifft
  """ Entscheid {a} wird von Gericht {g} getroffen """
  g: gericht
  a: akt

event beurteilt
  """ Gericht {g} beurteilt Beschwerde {b} """
  g: gericht
  b: beschwerde

event stelltAuslieferungsersuchen
  """ Staat {s} stellt ein Auslieferungsersuchen gegen Person {p} """
  s: staat
  p: person

event suchtSchutz
  """ Person {p} sucht Schutz vor Staat {s} """
  p: person
  s: staat

internal predicate zulaessig
  """ Beschwerde {b} ist bei Gericht {g} zulässig """
  g: gericht
  b: beschwerde

predicate oeffentlichesRecht
  """ Akt {a} ist ein Entscheid in Angelegenheiten des öffentlichen Rechts """
  a: akt

predicate kantonalerErlass
  """ Akt {a} ist ein kantonaler Erlass """
  a: akt

predicate betrifft
  """ Akt {a} betrifft {bet} """
  a: akt
  bet: gegenstand

predicate betrifftPerson
  """ Akt {a} betrifft Person {p} """
  a: akt
  p: person

predicate gebiet
  """ Akt {a} ist ein Entscheid auf dem Gebiet {geb} """
  a: akt
  geb: gebiet

predicate beurteilungsAnspruch
  """ {r} räumt einen Anspruch auf gerichtliche Beurteilung von Akt {a} ein """
  r: recht
  a: akt

predicate raeumtAnspruchEin
  """ {r} räumt einen Anspruch auf {g} ein """
  r: recht
  g: gegenstand

predicate bewilligung
  """ {g} ist eine Bewilligung """
  g: gegenstand

section "3"
article "82"

rule
  whenever
    beurteilt(g, b)
  oblige
    zulaessig(g, b)
  

paragraph "1"
point "a"

rule
  whenever
    anfechtungsObjekt(b, a)
    oeffentlichesRecht(a)
  constitute
    zulaessig("Bundesgericht", b)

point "b"

rule
  whenever
    anfechtungsObjekt(b, a)
    kantonalerErlass(a)
  constitute
    zulaessig("Bundesgericht", b)

point "c"

rule
  whenever
    anfechtungsObjekt(b, a)
    betrifft(a, "politische Stimmberechtigung") OR betrifft(a, "Volkswahlen") OR betrifft(a, "Volksabstimmungen")
  constitute
    zulaessig("Bundesgericht", b)

article "83"
paragraph "1"
point "a"

rule
  whenever
    gebiet(a, "auswärtige Angelegenheiten")
    NOT beurteilungsAnspruch("Völkerrecht", a)
  except "82(1)(a)"
  
point "b"

rule
  whenever
    betrifft(a, "ordentliche Einbürgerung")
  except "82(1)(a)"

point "c"
subpoint "1"

rule
  whenever
    gebiet(a, "Ausländerrecht")
    betrifft(a, "Einreise")
  except "82(1)(a)"

subpoint "2"

rule
  whenever
    gebiet(a, "Ausländerrecht")
    betrifft(a, bew)
    bewilligung(bew)
    NOT raeumtAnspruchEin("Bundesrecht", bew)
    NOT raeumtAnspruchEin("Völkerrecht", bew)
  except "82(1)(a)"

subpoint "3"

rule
  whenever
    gebiet(a, "Ausländerrecht")
    betrifft(a, "vorläufige Aufnahme")
  except "82(1)(a)"

subpoint "4"

rule
  whenever
    gebiet(a, "Ausländerrecht")
    betrifft(a, "Ausweisung (nach Art. 121 Abs. 2 BV)") OR betrifft(a, "Wegweisung")
  except "82(1)(a)"

subpoint "5"

rule
  whenever
    gebiet(a, "Ausländerrecht")
    betrifft(a, "Abweichungen von den Zulassungsvoraussetzungen")
  except "82(1)(a)"

subpoint "6"

rule
  whenever
    gebiet(a, "Ausländerrecht")
    betrifft(a, "Verlängerung der Grenzgängerbewilligung") OR betrifft(a, "Kantonswechsel") OR betrifft(a, "Stellenwechsel von Personen mit Grenzgängerbewilligung") OR betrifft(a, "Erteilung von Reisepapieren an schriftenlose AusländerInnen")
  except "82(1)(a)"

point "d"
  
subpoint "1"

rule
  whenever
    gebiet(a, "Asyl")
    ONCE trifft("Bundesverwaltungsgericht", a)
    NOT (EXISTS p. EXISTS s. betrifftPerson(a, p) AND (suchtSchutz(p, s) AND ONCE (stelltAuslieferungsersuchen(s, p))))
  except "82(1)(a)"
  
subpoint "2"

rule
  whenever
    gebiet(a, "Asyl")
    ONCE trifft("kantonale Vorinstanz", a)
    betrifft(a, bew)
    bewilligung(bew)
    NOT (raeumtAnspruchEin("Bundesrecht", bew))
    NOT (raeumtAnspruchEin("Völkerrecht", bew))
  except "82(1)(a)"

point "e"

rule
  whenever
    betrifft(a, "Verweigerung der Ermächtigung zur Strafverfolgung von Behördenmitgliedern oder von Bundespersonal")
  except "82(1)(a)"

point "f"
  
subpoint "1"
  
note "Die Beschwerde ist unzulässig gegen: [...] Entscheide auf dem Gebiet der öffentlichen Beschaffungen, wenn: [...] 1. sich keine Rechtsfrage von grundsätzlicher Bedeutung stellt; vorbehalten bleiben Beschwerden gegen Beschaffungen des Bundesverwaltungsgerichts, des Bundesstrafgerichts, des Bundespatentgerichts, der Bundesanwaltschaft sowie der oberen kantonalen Gerichtsinstanzen, oder"
subpoint "2"
note "Die Beschwerde ist unzulässig gegen: [...] Entscheide auf dem Gebiet der öffentlichen Beschaffungen, wenn: [...] 2. der geschätzte Wert des zu vergebenden Auftrags den massgebenden Schwellenwert nach Artikel 52 Absatz 1 in Verbindung mit Anhang 4 Ziffer 2 des Bundesgesetzes vom 21. Juni 2019 SR 172.056.1 über das öffentliche Beschaffungswesen nicht erreicht;"
point "fbis"
note "Die Beschwerde ist unzulässig gegen: [...] f bis . Eingefügt durch Ziff. I 2 des BG vom 16. März 2012 über den zweiten Schritt der Bahnreform 2, in Kraft seit 1. Juli 2013 ( AS 2012 5619 , 2013 1603 ; BBl 2011 911 ). Entscheide des Bundesverwaltungsgerichts über Verfügungen nach Artikel 32 i des Personenbeförderungsgesetzes vom 20. März 2009 SR 745.1 ;"
point "g"
note "Die Beschwerde ist unzulässig gegen: [...] g. Entscheide auf dem Gebiet der öffentlich-rechtlichen Arbeitsverhältnisse, wenn sie eine nicht vermögensrechtliche Angelegenheit, nicht aber die Gleichstellung der Geschlechter betreffen;"
point "h"
note "Die Beschwerde ist unzulässig gegen: [...] h. Fassung gemäss Anhang Ziff. 1 des Steueramtshilfegesetzes vom 28. Sept. 2012, in Kraft seit 1. Febr. 2013 ( AS 2013 231 ; BBl 2011 6193 ). Entscheide auf dem Gebiet der internationalen Amtshilfe, mit Ausnahme der Amtshilfe in Steuersachen;"
point "i"
note "Die Beschwerde ist unzulässig gegen: [...] i. Entscheide auf dem Gebiet des Militär-, Zivil- und Zivilschutzdienstes;"
point "j"
note "Die Beschwerde ist unzulässig gegen: [...] j. Fassung gemäss Anhang 2 Ziff. II 1 des Landesversorgungsgesetzes vom 17. Juni 2016, in Kraft seit 1. Juni 2017 ( AS 2017 3097 ; BBl 2014 7119 ). Entscheide auf dem Gebiet der wirtschaftlichen Landesversorgung, die bei schweren Mangellagen getroffen worden sind;"
point "k"
note "Die Beschwerde ist unzulässig gegen: [...] k. Entscheide betreffend Subventionen, auf die kein Anspruch besteht;"
point "l"
note "Die Beschwerde ist unzulässig gegen: [...] l. Entscheide über die Zollveranlagung, wenn diese auf Grund der Tarifierung oder des Gewichts der Ware erfolgt;"
point "m"
note "Die Beschwerde ist unzulässig gegen: [...] m. Fassung gemäss Ziff. I 1 des BG vom 20. Juni 2014, in Kraft seit 1. Jan. 2016  ( AS 2015 9 ; BBl 2013 8435 ). Entscheide über die Stundung oder den Erlass von Abgaben; in Abweichung davon ist die Beschwerde zulässig gegen Entscheide über den Erlass der direkten Bundessteuer oder der kantonalen oder kommunalen Einkommens- und Gewinnsteuer, wenn sich eine Rechtsfrage von grundsätzlicher Bedeutung stellt oder es sich aus anderen Gründen um einen besonders bedeutenden Fall handelt;"
point "n"
subpoint "1"
note "Die Beschwerde ist unzulässig gegen: [...] Entscheide auf dem Gebiet der Kernenergie betreffend: [...] 1. das Erfordernis einer Freigabe oder der Änderung einer Bewilligung oder Verfügung,"
subpoint "2"
note "Die Beschwerde ist unzulässig gegen: [...] Entscheide auf dem Gebiet der Kernenergie betreffend: [...] 2. die Genehmigung eines Plans für Rückstellungen für die vor Ausserbetriebnahme einer Kernanlage anfallenden Entsorgungskosten,"
subpoint "3"
note "Die Beschwerde ist unzulässig gegen: [...] Entscheide auf dem Gebiet der Kernenergie betreffend: [...] 3. Freigaben;"
point "o"
note "Die Beschwerde ist unzulässig gegen: [...] o. Entscheide über die Typengenehmigung von Fahrzeugen auf dem Gebiet des Strassenverkehrs;"
point "p"
subpoint "1"
note "Die Beschwerde ist unzulässig gegen: [...] Entscheide des Bundesverwaltungsgerichts auf dem Gebiet des Fernmeldeverkehrs, des Radios und des Fernsehens sowie der Post betreffend: Fassung gemäss Anhang Ziff. II 1 des Postgesetzes vom 17. Dez. 2010, in Kraft seit  1. Okt. 2012 ( AS 2012 4993 ; BBl 2009 5181 ). [...] 1. Konzessionen, die Gegenstand einer öffentlichen Ausschreibung waren,"
subpoint "2"
note "Die Beschwerde ist unzulässig gegen: [...] Entscheide des Bundesverwaltungsgerichts auf dem Gebiet des Fernmeldeverkehrs, des Radios und des Fernsehens sowie der Post betreffend: Fassung gemäss Anhang Ziff. II 1 des Postgesetzes vom 17. Dez. 2010, in Kraft seit  1. Okt. 2012 ( AS 2012 4993 ; BBl 2009 5181 ). [...] 2. Streitigkeiten nach Artikel 11 a des Fernmeldegesetzes vom 30. April 1997 SR 784.10 ,"
subpoint "3"
note "Die Beschwerde ist unzulässig gegen: [...] Entscheide des Bundesverwaltungsgerichts auf dem Gebiet des Fernmeldeverkehrs, des Radios und des Fernsehens sowie der Post betreffend: Fassung gemäss Anhang Ziff. II 1 des Postgesetzes vom 17. Dez. 2010, in Kraft seit  1. Okt. 2012 ( AS 2012 4993 ; BBl 2009 5181 ). [...] 3. Eingefügt durch Anhang Ziff. II 1 des Postgesetzes vom 17. Dez. 2010, in Kraft seit  1. Okt. 2012 ( AS 2012 4993 ; BBl 2009 5181 ). Streitigkeiten nach Artikel 8 des Postgesetzes vom 17. Dezember 2010 SR 783.0 ;"
point "q"
subpoint "1"
note "Die Beschwerde ist unzulässig gegen: [...] Entscheide auf dem Gebiet der Transplantationsmedizin betreffend: [...] 1. die Aufnahme in die Warteliste,"
subpoint "2"
note "Die Beschwerde ist unzulässig gegen: [...] Entscheide auf dem Gebiet der Transplantationsmedizin betreffend: [...] 2. die Zuteilung von Organen;"
point "r"
note "Die Beschwerde ist unzulässig gegen: [...] r. Entscheide auf dem Gebiet der Krankenversicherung, die das Bundesverwaltungsgericht gestützt auf Artikel 34 Berichtigt von der Redaktionskommission der BVers (Art. 58 Abs. 1 ParlG – SR 171.10 ). des Verwaltungsgerichtsgesetzes vom 17. Juni 2005 SR 173.32 . Dieser Art. ist aufgehoben. Siehe heute: Art. 33 Bst. i VGG in Verbindung mit Art. 53 Abs. 1 des BG vom 18. März 1994 über die Krankenversicherung  ( SR 832.10 ). (VGG) getroffen hat;"
point "s"
subpoint "1"
note "Die Beschwerde ist unzulässig gegen: [...] Entscheide auf dem Gebiet der Landwirtschaft betreffend: [...] 1. Aufgehoben durch Anhang Ziff. 1 des BG vom 22. März 2013, mit Wirkung seit  1. Jan. 2014 ( AS 2013 3463 3863 ; BBl 2012 2075 ). …"
subpoint "2"
note "Die Beschwerde ist unzulässig gegen: [...] Entscheide auf dem Gebiet der Landwirtschaft betreffend: [...] 2. die Abgrenzung der Zonen im Rahmen des Produktionskatasters;"
point "t"
note "Die Beschwerde ist unzulässig gegen: [...] t. Entscheide über das Ergebnis von Prüfungen und anderen Fähigkeitsbewertungen, namentlich auf den Gebieten der Schule, der Weiterbildung und der Berufsausübung;"
point "u"
note "Die Beschwerde ist unzulässig gegen: [...] u. Eingefügt durch Anhang Ziff. 3 des Finanzmarktaufsichtsgesetzes vom 22. Juni 2007  ( AS 2008 5207 ; BBl 2006 2829 ). Fassung gemäss Anhang Ziff. 1 des Finanzmarktinfrastrukturgesetzes vom 19. Juni 2015, in Kraft seit 1. Jan. 2016 ( AS 2015 5339 ; BBl 2014 7483 ). Entscheide auf dem Gebiet der öffentlichen Kaufangebote (Art. 125‒141 des Finanzmarktinfrastrukturgesetzes vom 19. Juni 2015 SR 958.1 );"
point "v"
note "Die Beschwerde ist unzulässig gegen: [...] v. Eingefügt durch Anhang Ziff. 3 des Finanzmarktaufsichtsgesetzes vom 22. Juni 2007,  in Kraft seit 1. Jan. 2009 ( AS 2008 5207 ; BBl 2006 2829 ). Entscheide des Bundesverwaltungsgerichts über Meinungsverschiedenheiten zwischen Behörden in der innerstaatlichen Amts- und Rechtshilfe;"
point "w"
note "Die Beschwerde ist unzulässig gegen: [...] w. Eingefügt durch Anhang Ziff. II 1 des Energiegesetzes vom 30. Sept. 2016, in Kraft seit 1. Jan. 2018 ( AS 2017 6839 ; BBl 2013 7561 ). Entscheide auf dem Gebiet des Elektrizitätsrechts betreffend die Plangenehmigung von Starkstromanlagen und Schwachstromanlagen und die Entscheide auf diesem Gebiet betreffend Enteignung der für den Bau oder Betrieb solcher Anlagen notwendigen Rechte , wenn sich keine Rechtsfrage von grundsätzlicher Bedeutung stellt;"
point "x"
note "Die Beschwerde ist unzulässig gegen: [...] x. Eingefügt durch Art. 21 Abs. 2 des BG vom 30. Sept. 2016 über die Aufarbeitung der fürsorgerischen Zwangsmassnahmen und Fremdplatzierungen vor 1981, in Kraft seit  1. April 2017 ( AS 2017 753 ; BBl 2016 101 ). Entscheide betreffend die Gewährung von Solidaritätsbeiträgen nach dem Bundesgesetz vom 30. September 2016 SR 211.223.13 über die Aufarbeitung der fürsorgerischen Zwangsmassnahmen und Fremdplatzierungen vor 1981, ausser wenn sich eine Rechtsfrage von grundsätzlicher Bedeutung stellt oder aus anderen Gründen ein besonders bedeutender Fall vorliegt;"
point "y"
note "Die Beschwerde ist unzulässig gegen: [...] y. Eingefügt durch Art. 36 Abs. 2 des BG vom 18. Juni 2021 über die Durchführung von internationalen Abkommen im Steuerbereich, in Kraft seit 1. Jan. 2022 ( AS 2021 703 ; BBl 2020 9219 ). Entscheide des Bundesverwaltungsgerichts in Verständigungsverfahren zur Vermeidung einer den anwendbaren internationalen Abkommen im Steuerbereich nicht entsprechenden Besteuerung;"
point "z"
note "Die Beschwerde ist unzulässig gegen: [...] z. Eingefügt durch Ziff. I 2 des BG vom 16. Juni 2023 über die Beschleunigung der Bewilligungsverfahren für Windenergieanlagen, in Kraft seit 1. Febr. 2024 ( AS 2023 804 ; BBl 2023 344 , 588 ). Entscheide betreffend die in Artikel 71 c Absatz 1 Buchstabe b des Energiegesetzes vom 30. September 2016 SR 730.0 genannten Baubewilligungen und notwendigerweise damit zusammenhängenden in der Kompetenz der Kantone liegenden Bewilligungen für Windenergieanlagen von nationalem Interesse, wenn sich keine Rechtsfrage von grundsätzlicher Bedeutung stellt."
article "84"
paragraph "1"
note " Gegen einen Entscheid auf dem Gebiet der internationalen Rechtshilfe in Strafsachen ist die Beschwerde nur zulässig, wenn er eine Auslieferung, eine Beschlagnahme, eine Herausgabe von Gegenständen oder Vermögenswerten oder eine Übermittlung von Informationen aus dem Geheimbereich betrifft und es sich um einen besonders bedeutenden Fall handelt."
paragraph "2"
note " Ein besonders bedeutender Fall liegt insbesondere vor, wenn Gründe für die Annahme bestehen, dass elementare Verfahrensgrundsätze verletzt worden sind oder das Verfahren im Ausland schwere Mängel aufweist."
article "a"
paragraph "1"
note "Gegen einen Entscheid auf dem Gebiet der internationalen Amtshilfe in Steuersachen ist die Beschwerde nur zulässig, wenn sich eine Rechtsfrage von grundsätzlicher Bedeutung stellt oder wenn es sich aus anderen Gründen um einen besonders bedeutenden Fall im Sinne von Artikel 84 Absatz 2 handelt."
article "85"
paragraph "1"
point "a"
note " In vermögensrechtlichen Angelegenheiten ist die Beschwerde unzulässig: [...] a. auf dem Gebiet der Staatshaftung, wenn der Streitwert weniger als 30 000 Franken beträgt;"
point "b"
note " In vermögensrechtlichen Angelegenheiten ist die Beschwerde unzulässig: [...] b. auf dem Gebiet der öffentlich-rechtlichen Arbeitsverhältnisse, wenn der Streitwert weniger als 15 000 Franken beträgt."
paragraph "2"
note " Erreicht der Streitwert den massgebenden Betrag nach Absatz 1 nicht, so ist die Beschwerde dennoch zulässig, wenn sich eine Rechtsfrage von grundsätzlicher Bedeutung stellt."
article "86"
paragraph "1"
point "a"
note " Die Beschwerde ist zulässig gegen Entscheide: [...] a. des Bundesverwaltungsgerichts;"
point "b"
note " Die Beschwerde ist zulässig gegen Entscheide: [...] b. des Bundesstrafgerichts;"
point "c"
note " Die Beschwerde ist zulässig gegen Entscheide: [...] c. der unabhängigen Beschwerdeinstanz für Radio und Fernsehen;"
point "d"
note " Die Beschwerde ist zulässig gegen Entscheide: [...] d. letzter kantonaler Instanzen, sofern nicht die Beschwerde an das Bundesverwaltungsgericht zulässig ist."
paragraph "2"
note " Die Kantone setzen als unmittelbare Vorinstanzen des Bundesgerichts obere Gerichte ein, soweit nicht nach einem anderen Bundesgesetz Entscheide anderer richterlicher Behörden der Beschwerde an das Bundesgericht unterliegen."
paragraph "3"
note " Für Entscheide mit vorwiegend politischem Charakter können die Kantone anstelle eines Gerichts eine andere Behörde als unmittelbare Vorinstanz des Bundesgerichts einsetzen."
article "87"
paragraph "1"
note " Gegen kantonale Erlasse ist unmittelbar die Beschwerde zulässig, sofern kein kantonales Rechtsmittel ergriffen werden kann."
paragraph "2"
note " Soweit das kantonale Recht ein Rechtsmittel gegen Erlasse vorsieht, findet Artikel 86 Anwendung."
article "88"
paragraph "1"
point "a"
note " Beschwerden betreffend die politische Stimmberechtigung der Bürger und Bürgerinnen sowie betreffend Volkswahlen und ‑abstimmungen sind zulässig: [...] a. in kantonalen Angelegenheiten gegen Akte letzter kantonaler Instanzen;"
point "b"
note " Beschwerden betreffend die politische Stimmberechtigung der Bürger und Bürgerinnen sowie betreffend Volkswahlen und ‑abstimmungen sind zulässig: [...] b. in eidgenössischen Angelegenheiten gegen Verfügungen der Bundeskanzlei und Entscheide der Kantonsregierungen."
paragraph "2"
note " Die Kantone sehen gegen behördliche Akte, welche die politischen Rechte der Stimmberechtigten in kantonalen Angelegenheiten verletzen können, ein Rechtsmittel vor. Diese Pflicht erstreckt sich nicht auf Akte des Parlaments und der Regierung."
article "89"
paragraph "1"
point "a"
note " Zur Beschwerde in öffentlich-rechtlichen Angelegenheiten ist berechtigt, wer: [...] a. vor der Vorinstanz am Verfahren teilgenommen hat oder keine Möglichkeit zur Teilnahme erhalten hat;"
point "b"
note " Zur Beschwerde in öffentlich-rechtlichen Angelegenheiten ist berechtigt, wer: [...] b. durch den angefochtenen Entscheid oder Erlass besonders berührt ist; und"
point "c"
note " Zur Beschwerde in öffentlich-rechtlichen Angelegenheiten ist berechtigt, wer: [...] c. ein schutzwürdiges Interesse an dessen Aufhebung oder Änderung hat."
paragraph "2"
point "a"
note " Zur Beschwerde sind ferner berechtigt: [...] a. die Bundeskanzlei, die Departemente des Bundes oder, soweit das Bundesrecht es vorsieht, die ihnen unterstellten Dienststellen, wenn der angefochtene Akt die Bundesgesetzgebung in ihrem Aufgabenbereich verletzen kann;"
point "b"
note " Zur Beschwerde sind ferner berechtigt: [...] b. das zuständige Organ der Bundesversammlung auf dem Gebiet des Arbeitsverhältnisses des Bundespersonals;"
point "c"
note " Zur Beschwerde sind ferner berechtigt: [...] c. Gemeinden und andere öffentlich-rechtliche Körperschaften, wenn sie die Verletzung von Garantien rügen, die ihnen die Kantons- oder Bundesverfassung gewährt;"
point "d"
note " Zur Beschwerde sind ferner berechtigt: [...] d. Personen, Organisationen und Behörden, denen ein anderes Bundesgesetz dieses Recht einräumt."
paragraph "3"
note " In Stimmrechtssachen (Art. 82 Bst. c) steht das Beschwerderecht ausserdem jeder Person zu, die in der betreffenden Angelegenheit stimmberechtigt ist."
