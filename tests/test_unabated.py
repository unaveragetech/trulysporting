from unabated import tag_link


def test_tag_keeps_path_and_replaces_existing_campaign():
    url = "https://www.gambly.com/deeplink/odds/4/16931467691/3.5"
    assert tag_link(url, "ABC") == url + "?utm_campaign=ABC"
    assert tag_link(url + "?utm_campaign=old&x=1", "ABC") == url + "?x=1&utm_campaign=ABC"


def test_no_code_or_link_means_no_link():
    assert tag_link("https://www.gambly.com/deeplink/odds/1/9/_", "") is None
    assert tag_link(None, "ABC") is None
