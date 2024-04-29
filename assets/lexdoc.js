const PREF_FORMULA = "lex-subformula";
const PREF_READING = "lex-subformula-reading";
const LEN_PREF_FORMULA = PREF_FORMULA.length;
const LEN_PREF_READING = PREF_READING.length;

function mouseenter_formula() {
    let id = $(this).attr('id');
    if (id.startsWith(PREF_FORMULA)) {
	let other_id = PREF_READING + id.substring(LEN_PREF_FORMULA);
	$("#" + id).addClass("lex-subformula-active");
	$("#" + other_id).addClass("lex-subformula-reading-active");
    }
}

function mouseleave_formula() {
    let id = $(this).attr('id');
    if (id.startsWith(PREF_FORMULA)) {
	let other_id = PREF_READING + id.substring(LEN_PREF_FORMULA);
	$("#" + id).removeClass("lex-subformula-active");
	$("#" + other_id).removeClass("lex-subformula-reading-active");
    }
}

function mouseenter_reading() {
    let id = $(this).attr('id');
    if (id.startsWith(PREF_READING)) {
	let other_id = PREF_FORMULA + id.substring(LEN_PREF_READING);
	$("#" + other_id).addClass("lex-subformula-active");
	$("#" + id).addClass("lex-subformula-reading-active");
    }
}

function mouseleave_reading() {
    let id = $(this).attr('id');
    if (id.startsWith(PREF_READING)) {
	let other_id = PREF_FORMULA + id.substring(LEN_PREF_READING);
	$("#" + other_id).removeClass("lex-subformula-active");
	$("#" + id).removeClass("lex-subformula-reading-active");
    }
}

$(".lex-subformula").on({
    mouseenter: mouseenter_formula,
    mouseleave: mouseleave_formula
})

$(".lex-subformula-reading").on({
    mouseenter: mouseenter_reading,
    mouseleave: mouseleave_reading
})

$(".lex-type-fix").on({
    mouseenter: mouseenter_formula,
    mouseleave: mouseleave_formula
})

$(".lex-type-fix-reading").on({
    mouseenter: mouseenter_reading,
    mouseleave: mouseleave_reading
})

