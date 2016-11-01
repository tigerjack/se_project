module Users

/**
	Users
*/
abstract sig User {}

sig RegisteredUser extends User {
	id: Int,
	// A user can only use one vehicle at a given time
	// usedVehicle: lone Vehicle
}
fact idAreUniques {
	all ru1, ru2: RegisteredUser | (ru1 != ru2) =>
		(ru1.id != ru2.id)
}


//Uneseful ??
// sig UnregisteredUser extends User {}
