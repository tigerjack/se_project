module Utilities

/**
	Geolocalization
*/
sig Position {
	latitude: one Int,
	longitude: one Int
}

sig Segment {
	start: one Position,
	end: one Position
}
{start != end}


/**
	Fee
*/
abstract sig Fee {}


sig TimeFee extends Fee {
	amountPerMinutes: Int
}

sig FixedFee {
	amount: Int
}
{amount > 0}

sig PenaltyFee extends FixedFee {}

sig DiscountFeePercentage extends FixedFee {}
{amount <= 100}
