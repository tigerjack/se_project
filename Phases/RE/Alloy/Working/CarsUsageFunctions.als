module CarUsageFunctions
open Cars
open Persons
open BankingFunctions
open Time

/**
	SIGNATURES
*/


one sig ReservationData {
	// for a given ReservingData and at a given Time, each Car is associated (i.e.
	// reserved) by at most one User and viceversa
	reservations: (User lone -> lone Car ) -> one Time
}
/*
{
	User.(reservations.Time).currentState = Available
}
*/
one sig UsingCarStartTime {
	// for a given ReservingData and at a given Time, each Car is associated (i.e.
	// reserved) by at most one User and viceversa
	usingDatas: (User lone -> lone Car ) -> one Time
}

/*
fact carsInUseInUsingData {
	all c: Car | one r: ReservingCarTime | c.currentState = InUse iff c in User.(r.reservations.Time)
}
*/
fact twoDifferentUsersCantReserveTheSameCarAtTheSameTime {
	all r: ReservationData, t: Time | no disj u1, u2: User | 
		u1.(r.reservations.t) & u2.(r.reservations.t) = none
}

//
fact twoDifferentCarsCantBeReserveAtTheSameTimeByTheSameUser {
	all r: ReservationData, t: Time | no disj u1, u2: User | 
		u1.(r.reservations.t) & u2.(r.reservations.t) = none
}

fact ReservationsAndUsingDatasetAreDisjunct {
	no ReservationData.reservations & UsingCarStartTime.usingDatas
}

/**
	PREDICATES
*/
pred init() {
	no (ReservationData.reservations).first and
	no (UsingCarStartTime.usingDatas).first
}

pred canReserveACar[u: User, c: Car, t: Time] {
	c.currentState = Available and
//	u not in Car.usedSeats and
//	u not in DrivingCarStartTime.drivingDatas.t.Car and 
	no u.((ReservationData.reservations).t) and
	no ((ReservationData.reservations).t).c
}
run canReserveACar for 3

pred reserveACar[u: User, c: Car, t: Time, r, r': ReservationData] {
//	canReserveACar[u, c, t] and
	r'.reservations = r.reservations + (u -> c) -> t
}
run reserveACar for 3


pred show() {
	Car in User.(ReservationData.reservations.Time)
}

run show for 3
