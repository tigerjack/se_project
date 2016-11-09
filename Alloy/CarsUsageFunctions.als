module CarUsageFunctions
open Cars
open Users

/**
	SIGNATURES
*/
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
	passengersMinutesRange >= 0
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

/**
	FACTS
*/
fact drivenCarsStateShouldBeInUse {
	all d: DrivingData, c: Car | (d.isDriving).c != none iff 
		c.currentState = InUse
}

fact reservedCarsStateShouldBeReserved {
	all r: ReservationData, c: Car | (r.hasReserved).c != none iff 
		c.currentState = Reserved
}

/**
	ASSERTS
*/
assert allDrivenCarsStateIsInUse {
	all c: Car | one d: DrivingData | c in User.(d.isDriving)
}


assert allDrivenCarsHaveADriver {
	all c: Car, d: DrivingData | c in User.(d.isDriving) implies 
		(d.isDriving).c != none
}



check allDrivenCarsStateIsInUse for 5 but 7 Int
check allDrivenCarsHaveADriver for 5 but 8 int

/**
	PREDICATES
*/

/*
pred canReserveACar[u: User, c: Car] {
	all r: ReservationData | not u in (r.hasReserved).Car and 
	(c.currentState = Available or c.currentState = Plugged)
}


pred addReservationData[r, r': ReservationData, u: User, c: Car] {
	(r'.hasReserved = r.hasReserved + u -> c) &&
	r.reservationMinutes = 0
}

/*
pred addDrivingData[d, d': DrivingData, u: User, c: Car] {
	
	(r'.hasReserved = r.hasReserved + u -> c) &&
	r.reservationMinutes = 0

}

/*
fun driveACar[u: User, c: Car]: DrivingData {

}

fun reserveACar[u: User, c: Car]: ReservationData {
	
}
*/

run canReserveACar for 3 but 8 Int
run addReservationData for 3 but 8 Int

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
