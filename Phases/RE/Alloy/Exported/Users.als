module Users
/**
	SIGNATURES
*/
abstract sig Person {}
sig Visitor extends Person {}
sig User extends Person {
	
//	code: one UserCode,
//	email: one Email
	// Not interested in other parameters
}

/**
	PREDICATES/FUNCTIONS
*/
pred show() {
	#User > 0
}

run show for 25

/*

sig Email {}
sig UserCode extends Code {}

fact codesAreUnique {
	all u1, u2: User | (u1 != u2) implies
		(u1.code != u2.code)
}
fact userCodesAreAssociatedToOneUser
{
	all uc: UserCode | one u: User | uc in u.code
}
fact userMailsAreUnique {
	all u1, u2: User | (u1 != u2) implies
		(u1.email != u2.email)
}


*/
