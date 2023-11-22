/*
 * GOALS SUI QUALI CI FOCALIZZIAMO:
 * G1
 * G2
 * G3
 * G8
 * G9
 */

-- All possible Tournament Status
abstract sig TournamentStatus {}
one sig SUBSCRIPTION_TOURNAMENT extends TournamentStatus {}
one sig ACTIVE_TOURNAMENT extends TournamentStatus {}
one sig NON_ENDABLE extends TournamentStatus {}
one sig ENDED_TOURNAMENT extends TournamentStatus {}

-- All possible Battle Status
abstract sig BattleStatus {}
one sig SUBSCRIPTION_BATTLE extends BattleStatus {}
one sig ACTIVE_BATTLE extends BattleStatus {}
one sig CONSOLIDATION_STAGE extends BattleStatus {}
one sig ENDED_BATTLE extends BattleStatus {}

-- All possible Badge Status
abstract sig BadgeStatus {}
one sig CREATED extends BadgeStatus {}
one sig ASSIGNED extends BadgeStatus {}
one sig BADGE_INVALID extends BadgeStatus {}

-- All possible Battle Invitation Status
abstract sig BattleInvitationStatus {}
one sig VALID extends BattleInvitationStatus {}
one sig ACCEPTED extends BattleInvitationStatus {}
one sig INVITATION_INVALID extends BattleInvitationStatus {}

--Boolean definition
abstract sig Bool {}
one sig True, False extends Bool {}

--Simplified Account view: only Username and Password
sig Username {}
sig Password {}

abstract sig Account {
	username : one Username,
	password : one Password
}

sig Educator extends Account {} -- TODO: dobbiamo aggiungere qualcosa?
sig Student extends Account {}

sig Tournament {
	status : one TournamentStatus,
	battles : set Battle,
	educators : some Educator,
	participants : set Student,
	creation_date : one Int,
	registration_deadline : one Int,
	badges : set Badge
} {registration_deadline > creation_date}

sig Battle {
	status : one BattleStatus,
	creation_date : one Int,
	registration_deadline : one Int,
	submission_deadline : one Int,
	creator : one Educator,
	participants : set Team,
	min_team_dim : one Int,
	max_team_dim : one Int
} {registration_deadline > creation_date and
	submission_deadline > registration_deadline and
	max_team_dim >= min_team_dim
}

sig Badge {
	status : one BadgeStatus,
	creator : one Educator,
	owner : lone Student
}

sig Team{
	members : some Student
}

sig BattleInvitation {
	status : one BattleInvitationStatus,
	team : one Team,
	student : one Student,
	battle : one Battle,
	invitation_date : one Int
} {
	invitation_date < battle.registration_deadline and
	invitation_date >= battle.creation_date
}

-- Used to model current time
sig currTime {
	time : one Int
} { time > 0 }

-- FACTS

-- Account:

-- No duplicate Usernames
fact {no disj a1, a2 : Account | a1.username = a2.username }
-- All Passwords belong to an Account
fact {all p : Password | one a : Account | a.password = p }

-- Tournament:

	-- All tournaments have at least  one Educator
	-- fact { all t : Tournament | one e : Educator | e in t.educators } -- ridondante?

-- All battles of one tournament has the creator that is one educator in that tournament
fact { all b : Battle | one t : Tournament | b in t.battles and
	( one e : Educator | e = b.creator and ( e in t.educators )) }

-- If there is at least one battle not ended the tournament can't be closed
fact { all t : Tournament | ( t.status = NON_ENDABLE ) iff ( one b : Battle | b in t.battles and
	b.status != ENDED_BATTLE ) }

-- One tournament has subscriptions open if the deadline for subscriptions has not been reached yet
fact { all t : Tournament | t.status = SUBSCRIPTION_TOURNAMENT implies
	t.registration_deadline > currTime.time }

-- If a tournament has been closed, it will be always closed
fact { all t : Tournament | always( t.status = ENDED_TOURNAMENT implies
	after always t.status = ENDED_TOURNAMENT ) }

-- During the subscription phase a tournament can't have battles
fact { all t : Tournament | t.status = SUBSCRIPTION_TOURNAMENT implies
	# t.battles = 0  } 

-- If a tournament is active or ended it has no battle that are not ended
fact { all t : Tournament | t.status = ACTIVE_TOURNAMENT or t.status = ENDED_TOURNAMENT implies
	no one b : Battle | b in t.battles and b.status != ENDED_BATTLE }























