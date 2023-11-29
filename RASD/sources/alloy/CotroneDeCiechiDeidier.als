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

sig Educator extends Account {
	createdTournaments : set Tournament
}
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
	max_team_dim : one Int,
	needs_manual_eval : one Bool,
	manual_eval_inserted : one Bool
} {registration_deadline > creation_date and
	submission_deadline > registration_deadline and
	max_team_dim >= min_team_dim
}

sig Badge {
	status : one BadgeStatus,
	creator : one Educator,
	owner : lone Student,
	creation_date : one Int
}

sig Team{
	members : some Student,
	subscription_date : one Int
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

-- No two tournaments are equal
fact { no disj t1, t2 : Tournament | t1 = t2 }

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
fact { all t : Tournament | ( t.status = ACTIVE_TOURNAMENT or t.status = ENDED_TOURNAMENT ) implies
	no b : Battle | b in t.battles and b.status != ENDED_BATTLE }

-- For all tournaments exists only one creator
fact { all t : Tournament | one e : Educator | e in t.educators and t in e.createdTournaments }

-- The creator of a badge in a specific tournament is the creator of that tournament
fact { all t : Tournament | all b : Badge | b in t.badges implies
	one e : Educator | e = b.creator and t in e.createdTournaments }

-- Battle:

-- No two battles are equal
fact { no disj b1, b2 : Battle | b1 = b2 }

-- All battles belong to a tournament
fact { all b : Battle | one t : Tournament | b in t.battles }

-- One battle has subscriptions open if the deadline for subscriptions has not been reached yet
fact { all b : Battle | b.status = SUBSCRIPTION_BATTLE implies
	b.registration_deadline > currTime.time }

-- A team can't register in a battle after the subscription phase
fact { all b : Battle | all t : Team | t in b.participants implies
	t.subscription_date < b.registration_deadline }

-- One battle is active if the deadline for submissions has not been reached yet
fact { all b : Battle | b.status = ACTIVE_BATTLE implies
	b.submission_deadline > currTime.time }

-- One battle is in consolidation phase if the deadline for submissions has been reached and it needs the manual evaluation
fact { all b : Battle | b.status = CONSOLIDATION_STAGE implies
	b.submission_deadline <= currTime.time and b.needs_manual_eval = True }

-- One battle is ended if the deadline for submissions has been reached and it doesn't need the manual evaluation or
--	the manual evaluation is inserted
fact { all b : Battle | b.status = CONSOLIDATION_STAGE implies
	b.submission_deadline <= currTime.time and ( b.needs_manual_eval = False or
	( b.needs_manual_eval = True and b.manual_eval_inserted = True )) }

-- If a battle has ended, it will be always ended
fact { all b : Battle | always( b.status = ENDED_BATTLE implies
	after always b.status = ENDED_BATTLE ) }

-- All the teams are made up by only students that are registered in the tournament of that battle
fact { all t : Tournament | all b : Battle | b in t.battles implies
	( one team : Team | team in b.participants and ( all s : Student | s in team.members implies s in t.participants )) } -- TODO: ok????

-- Badge:

-- All the badge of a tournament are created during the creation of the tournament
fact { all b : Badge | all t : Tournament | b in t.badges implies
	b.creation_date = t.creation_date }

-- Team:

-- If a student is in a team for a battle, it can't be also a member of another team
fact { no disj t1, t2 : Team | one b : Battle | ( t1 in b.participants and t2 in b.participants ) and
	( one s : Student | s in t1.members and s in t2.members ) }

pred Test {
	#Tournament = 1
	#Battle = 1
	#Educator = 1
	#Team = 2
	#Student = 2
}
run Test














