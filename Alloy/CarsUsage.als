module VehiclesUsage
open Cars
open Users


sig DrivingData {
	user: lone User,
	car: lone Car
}

sig ReservationData {
	user: lone User,
	car: lone Car,
	timestamp: Int
}
{timestamp > 0}


fact drivingVehicleStateShouldBeInUse {
	all d: DrivingData, c: Car | c in d.car implies c.currentState = InUse
}
/*
fact drivingVehiclesAndUsersAreNotUbiquituous {
	all d1, d2: DrivingData | d1 != d2 implies 
		d1.user != d2.user and
		d1.car != d2.car
}

fact reservedVehiclesAndUsersAreNotUbiquituous {
	all r1, r2: ReservationData | r1 != r2 implies 
		r1.user != r2.user and
		r1.car != r2.car
}
*/
fact reservedVehicleStateShouldBeReserved {
	all d: ReservationData | d.car.currentState = Reserved
}


pred canReserveACar[u: User, c: Car] {
	all r: ReservationData | not u in r.user and c.currentState = Available
}

/*
fun driveACar[u: User, c: Car]: DrivingData {

}
/*
fun reserveACar[u: User, c: Car]: ReservationData {
	
}
*/


pred show() {
	#ReservationData > 1
	#DrivingData > 1
	#Car = 3
}

run show for 10 but 8 Int



// Facts:
// if usedVehicle != 0, then the vehicle should have its state to Used
