module Cars
//open GPSUtilities
open Codes
/**
	Cars
*/



sig Car {
	code: one CarCode,
	battery: one Battery,
	plug: one Plug,
	seats: Int,
	usedSeats: Int,
//	currentPosition: one GPSPoint,
	currentState: one CarState
	// We assume there is one tye of plug, so we don't mention it.
	// If multiple plugs should be allowed, we have to modify this sig
}
{
	currentState != none
	seats > 0 and seats <=4 
	usedSeats >= 0 and usedSeats <= seats
	currentState = InUse implies usedSeats > 0
	currentState != InUse implies usedSeats = 0
	battery.statusPercentage = 0 implies currentState = Unavailable
}
fact codesAreUniques {
	all c1, c2: Car | (c1 != c2) implies (c1.code != c2.code)
}
fact carCodesAreAssociatedToOneCar
{
	all cc: CarCode | one c: Car | cc in c.code
}


sig Battery {
	statusPercentage: Int
}
{
	statusPercentage >= 0 statusPercentage <= 100
}
fact batteriesMustBeAssociatedToOneVehicle {
	all b: Battery | one c: Car | b in c.battery
}


sig Plug {} 
fact plugsMustBeAssociatedToOneVehicle {
	 all p: Plug | one c: Car | p in c.plug 
}

enum CarState {
	InUse, Available, Reserved, Unavailable, Plugged
}

pred show() {
	#Car = 5
	#Battery.statusPercentage = #Car

	
}

run show for 6 but 8 Int


