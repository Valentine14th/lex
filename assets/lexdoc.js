const PREF_FORMULA = "lex-subformula";
const PREF_READING = "lex-subformula-reading";
const LEN_PREF_FORMULA = PREF_FORMULA.length;
const LEN_PREF_READING = PREF_READING.length;

$(".lex-subformula").on({
    mouseenter: function() {
	let id = $(this).attr('id');
	if (id.startsWith(PREF_FORMULA)) {
	    let other_id = PREF_READING + id.substring(LEN_PREF_FORMULA);
	    $("#" + id).addClass("lex-subformula-active");
	    $("#" + other_id).addClass("lex-subformula-reading-active");
	}
    },
    mouseleave: function() {
	let id = $(this).attr('id');
	if (id.startsWith(PREF_FORMULA)) {
	    let other_id = PREF_READING + id.substring(LEN_PREF_FORMULA);
	    $("#" + id).removeClass("lex-subformula-active");
	    $("#" + other_id).removeClass("lex-subformula-reading-active");
	}
    }
})

$(".lex-subformula-reading").on({
    mouseenter: function() {
	let id = $(this).attr('id');
	if (id.startsWith(PREF_READING)) {
	    let other_id = PREF_FORMULA + id.substring(LEN_PREF_READING);
	    $("#" + other_id).addClass("lex-subformula-active");
	    $("#" + id).addClass("lex-subformula-reading-active");
	}
    },
    mouseleave: function() {
	let id = $(this).attr('id');
	if (id.startsWith(PREF_READING)) {
	    let other_id = PREF_FORMULA + id.substring(LEN_PREF_READING);
	    $("#" + other_id).removeClass("lex-subformula-active");
	    $("#" + id).removeClass("lex-subformula-reading-active");
	}
    }
})

