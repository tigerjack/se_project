module Users

/**
	Users
*/
abstract sig Person {}

sig User extends Person {
	id: Int,
	email: String,
	// Not interested in other parameters
	// A user can only use one vehicle at a given time
	// usedVehicle: lone Vehicle
}
fact idsAreUnique {
	all u1, u2: User | (u1 != u2) =>
		(u1.id != u2.id)
}

fact mailsAreUnique {
	all u1, u2: User | (u1 != u2) =>
		(u1.email != u2.email)
}

pred show() {}

run show for 25
