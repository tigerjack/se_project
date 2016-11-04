module Users
open Codes
/**
	Users
*/
sig Email {}

abstract sig Person {}

sig Visitor extends Person {}

sig User extends Person {
	code: one UserCode,
	email: one Email
	// Not interested in other parameters
	// A user can only use one vehicle at a given time
	// usedVehicle: lone Vehicle
}
fact idsAreUnique {
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

pred show() {
	#User > 0
}

run show for 25
