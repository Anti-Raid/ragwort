use crate::gc::Arena;
use crate::pair::Pairs;

use super::*;

struct UserId(u64);
struct ChannelId(u64);

static USER_ID: ExternalKind<UserId> = ExternalKind::by_value("user-id", |first, second| first.0 == second.0, |id| id.0);
/// A second kind whose values hash as user ids do, and are never equal to one.
static CHANNEL_ID: ExternalKind<ChannelId> = ExternalKind::by_value("channel-id", |first, second| first.0 == second.0, |id| id.0);
static HANDLE: ExternalKind<String> = ExternalKind::by_identity("handle");

#[test]
fn a_reference_holds_the_hosts_value_and_what_goes_with_it() {
    let mut arena = Arena::new(1 << 20, 1);
    arena.mutate(|mc| {
        let externals = ExternalRefs::new(mc);
        let kept = Pairs::new(mc).list(&[Value::TRUE]).unwrap();
        let handle = externals.make(&HANDLE, "a handle".to_string(), 8, kept).unwrap();
        assert_eq!(ExternalRef::of(handle.value(mc)), Some(handle));
        assert!(ExternalRef::of(kept).is_none() && externals.external(Value::NIL).is_none());
        assert_eq!((handle.name(mc), handle.data::<String>(mc).map(String::as_str), handle.data::<UserId>(mc).is_none()), ("handle", Some("a handle"), true));
        assert_eq!(handle.kept(mc), kept);
        mc.set_root(0, handle.value(mc));
    });
    // Both the host's value and the arena's value that goes with it outlive collections that move objects.
    arena.set_evacuate_all(true);
    arena.collect();
    arena.mutate(|mc| {
        let handle = ExternalRef::of(mc.root(0)).unwrap();
        assert_eq!(handle.data::<String>(mc).map(String::as_str), Some("a handle"));
        assert_eq!(Pairs::new(mc).elements(handle.kept(mc)).collect::<Vec<_>>(), [Value::TRUE]);
    });
}

#[test]
fn a_kind_says_when_two_references_are_equal() {
    Arena::new(1 << 20, 0).mutate(|mc| {
        let externals = ExternalRefs::new(mc);
        let user = |id| externals.make(&USER_ID, UserId(id), 0, Value::NIL).unwrap();
        let (ann, again, bo) = (user(7), user(7), user(8));
        assert!(ann != again && ann.same(mc, again) && again.same(mc, ann) && ann.same(mc, ann));
        assert!(!ann.same(mc, bo));
        assert_eq!((ann.hash(mc), again.hash(mc), bo.hash(mc)), (Some(7), Some(7), Some(8)));
        // A reference of another kind is never equal, whatever its value.
        let channel = externals.make(&CHANNEL_ID, ChannelId(7), 0, Value::NIL).unwrap();
        assert!(!ann.same(mc, channel) && !channel.same(mc, ann));
        assert_eq!((channel.name(mc), channel.hash(mc)), ("channel-id", Some(7)));
        // A kind with no equality of its own compares by identity.
        let handle = |text: &str| externals.make(&HANDLE, text.to_string(), 0, Value::NIL).unwrap();
        let (first, second) = (handle("same"), handle("same"));
        assert!(first.same(mc, first) && !first.same(mc, second) && !first.same(mc, ann));
        assert_eq!(first.hash(mc), None);
    });
}
