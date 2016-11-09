module BankingFunctions

/**
	SIGNATURES
*/
abstract sig Fee {}

sig TimeFee extends Fee {
	amountPerMinutes: Int
}

sig FixedFee {
	amount: Int
}
{amount > 0}

sig PercentageFee extends Fee {
	amount: Int
}
{amount >= 0 and amount <= 100}
