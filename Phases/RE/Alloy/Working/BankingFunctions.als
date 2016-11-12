module BankingFunctionalities

/**
	SIGNATURES
*/
abstract sig Fee {}

sig TimeFee extends Fee {}

sig FixedFee extends Fee {}

sig PercentageFee extends Fee {}

abstract sig Discount extends PercentageFee {}
sig PluggingDiscount, PassengersDiscount, HighBatteryDiscount extends Discount {}

abstract sig Surcharge extends FixedFee {}
sig ReservationExpirationSurcharge extends Surcharge {}
