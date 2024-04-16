# Default hierarchy:
# - law[0..]
#   -title[0..]
#     -chapter[0..]
#       - article[0..]
#         - paragraph[0..]
#           - point[0..]
#             - subpoint[0..]

law "GDPR" "General Data Protection Regulation"
chapter "1" "first chapter" # so far has no semantic meaning, could potentially be referred to in exceptions in the future
article "1" "article 1" # equivalently: article[0] "1" "article 1"
article[1] "1" "article sub-section 1"
paragraph "1" "paragraph 1"
rule
whenever
oblige

paragraph "2" "paragraph 2"
rule
whenever
constitute

chapter "2" "second chapter" # so far has no semantic meaning
article "2" "article 1"
paragraph "1" "paragraph 1"
rule
whenever
except "(1)"
# can not refer to itself (as it would not make sense)
# could refer to Art. 1
# cannot refer to anything below Art. 1
# -> thus it must be Art. 1
point "(1)" "point 1"
rule
whenever
oblige

paragraph "2" "paragraph 2"
rule
whenever
except "(1)" # "(2)(1)", "GDPR (1)", "GDPR (2)(1)"
# can refer to Art. 2 par. 1
# might also refer to Art. 1 (though maybe it should/can not)
# -> either we have to dismabiguate the label system more
# -> or we take the match that is "closest" to the current position
#    i.e. Art. 2 par. 1

paragraph "3" "paragraph 3"
rule
whenever
except "(1)(1)" # "(2)(1)(1)", "GDPR (1)(1)", "GDPR (2)(1)(1)"
# can refer to Art. 2 par. 1 point 1
# cannot refer to Art. 1 article[1] 1 ("GDPR (1)(1)")
#    because article[1] is outside the "current" scope

