module VehiclesUsage
open Cars
open Users

// SIGNATURES
abstract sig CarsUsageData {}

sig DrivingData extends CarsUsageData {
	isDriving: User lone -> lone Car,
	// The minutes passed from the driving start
	ridingMinutes: Int,
	// The range of minutes in which there is a passenger in the car
	passengersMinutesRange: Int
}
{
	ridingMinutes > 0
	passengersMinutes >= 0
}

sig ReservationData extends CarsUsageData {
	hasReserved: User lone -> lone Car,
	// The time passed from the reservation start
	reservationMinutes: Int
}
{
	reservationMinutes > 0 and reservationMinutes <= 60
}

sig PluggingData {
}

sig EndingRideData {
}

// FACTS

fact drivenCarsStateShouldBeInUse {
	all d: DrivingData, c: Car | (d.isDriving).c != none implies 
		c.currentState = InUse
}

fact reservedCarsStateShouldBeReserved {
	all r: ReservationData, c: Car | (r.hasReserved).c != none implies 
		c.currentState = Reserved
}

// ASSERT
assert allDrivenCarsStateIsInUse {
	all c: Car | one d: DrivingData | c in User.(d.isDriving)
}


assert allDrivenCarsHaveADriver {
	all c: Car, d: DrivingData | c in User.(d.isDriving) implies 
		(d.isDriving).c != none
}

check allDrivenCarsStateIsInUse for 5 but 7 Int
check allDrivenCarsHaveADriver for 5 but 8 int

// PREDICATES

/*
pred canReserveACar[u: User, c: Car] {
	all r: ReservationData | not u in r.user and c.currentState = Available
}

pred addReservation[r, r': ReservationData] {
	
	r' = r
}


fun driveACar[u: User, c: Car]: DrivingData {

}
/*
fun reserveACar[u: User, c: Car]: ReservationData {
	
}
*/


pred show() {
	#ReservationData > 0
	#DrivingData > 0
	#Car > 2
}

run show for 3 but 10 Int

/*
sig Timestamp{
	// Fake bcz we only generates a small number of integers
	fakeStamp: Int
}
*/
