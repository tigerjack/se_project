module BankingUtilities
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
{amount >=0 and amount <= 100}
